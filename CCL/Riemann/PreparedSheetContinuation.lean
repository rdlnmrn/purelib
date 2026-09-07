import CCL.Riemann.ReconditionedClearSheetContinuation
import CCL.Riemann.ExactQuadraticOwnerClearance
import CCL.Riemann.UniformSquareRootPreparation

/-!
# Diameter-prepared square-root continuation

Before each Rouché move, this checker refines the inherited square-root owner
to an explicitly requested squared diameter.  The move is tested against that
prepared owner's fresh clearance, and the endpoint is then reconditioned as
before.  Thus every accepted edge carries both kinds of quantitative data
needed by integration:

* the root occurrence used on the edge has a displayed small box; and
* the next edge starts from a fresh global owner of the same occurrence.

All requests and checks are finite rational data.
-/

namespace CCL.Riemann.PreparedSheetContinuation

open CCL.Riemann.BranchCuts
open CCL.Riemann.ExactQuadraticOwnerClearance

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Owner := CCL.Riemann.SquareRootContinuationChain.Owner
abbrev Endpoint := CCL.Riemann.ClearSheetContinuation.Subdivision.Endpoint
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev Named := CCL.ProgressiveTransducer.Named

/-- A moving quadratic reset is operationally the same root: its displayed
common owner is strictly inside both the completed source window and the
replacement window. -/
def movingRecenterRootEquivalent {parameter : Gaussian}
    (source : Owner parameter)
    (reset : MovingRecenter parameter source) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        source.parameterNonzero source)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        source.parameterNonzero reset.owner) := by
  let common := reset.bridgeOwner.refineAt 1
  have commonStrictBridge : common.track.initial.box.StrictInterior
      reset.bridgeOwner.track.initial.box := by
    change
      (reset.bridgeOwner.track.refine reset.bridgeOwner.track.initial
        (CCL.BoxedNameProcess.accuracyRadius
          (CCL.Riemann.CoherentRoot.stepTarget reset.bridgeOwner.track 0))
        (CCL.BoxedNameProcess.accuracyRadius_pos
          (CCL.Riemann.CoherentRoot.stepTarget_positive
            reset.bridgeOwner.track 0))).box.StrictInterior
        reset.bridgeOwner.track.initial.box
    exact reset.bridgeOwner.track.strict _ _ _
  have commonRefinesBridge : common.track.initial.box.Refines
      reset.bridgeOwner.track.initial.box :=
    reset.bridgeOwner.refineAt_initial_refines 1
  have sourceToCommon :=
    CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      source.parameterNonzero source.track common.track
        (commonStrictBridge.trans_refines reset.bridgeRefinesSource)
  have movedToCommon :=
    CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      source.parameterNonzero reset.owner.track common.track
        (reset.bridgeStrictOwner.of_refines commonRefinesBridge)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans sourceToCommon
    movedToCommon.symm

/-- Use a finite moving quadratic reset when its direct winding checks
succeed, and otherwise retain the input owner. -/
def recentered {parameter : Gaussian} (owner : Owner parameter) :
    Owner parameter :=
  match movingRecenter? owner with
  | none => owner
  | some reset => reset.owner

/-- A successful cached moving-reset computation identifies the owner used by
`recentered` without unfolding the reset search a second time. -/
theorem recentered_eq_of_movingRecenter_eq_some {parameter : Gaussian}
    (owner : Owner parameter) (reset : MovingRecenter parameter owner)
    (found : movingRecenter? owner = some reset) :
    recentered owner = reset.owner := by
  unfold recentered
  rw [found]

/-- A moving reset is a direct quadratic owner, while a failed reset retains
the input.  Hence recentering preserves the finite boundary-to-ambient
dominance invariant. -/
theorem recentered_ambientClearanceDominance {parameter : Gaussian}
    (owner : Owner parameter)
    (dominance : AmbientClearanceDominance owner) :
    AmbientClearanceDominance (recentered owner) := by
  unfold recentered
  generalize resetEq : movingRecenter? owner = reset
  cases reset with
  | none => exact dominance
  | some moved => exact moved.ownerDominance

/-- The optional moving reset cannot change the displayed root occurrence. -/
def recenteredRootEquivalent {parameter : Gaussian} (owner : Owner parameter) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        owner.parameterNonzero owner)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        owner.parameterNonzero (recentered owner)) := by
  unfold recentered
  generalize resetEq : movingRecenter? owner = reset
  cases reset with
  | none => exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  | some moved => exact movingRecenterRootEquivalent owner moved

/-- Retain a transported quadratic window while its displayed clearance meets
the next uniform floor, and run the finite moving reset only after that reserve
has been lost. -/
def retainedAtReserve {parameter : Gaussian} (owner : Owner parameter)
    (reserve : Coordinate) : Owner parameter :=
  if reserve <= owner.track.initial.clearance.bound then owner
  else recentered owner

/-- An explicit retained-clearance witness selects the no-reset branch
without reevaluating the moving-recenter search. -/
theorem retainedAtReserve_eq_self {parameter : Gaussian}
    (owner : Owner parameter) (reserve : Coordinate)
    (enough : reserve ≤ owner.track.initial.clearance.bound) :
    retainedAtReserve owner reserve = owner := by
  unfold retainedAtReserve
  rw [if_pos enough]

/-- Retention respects equality of the source owner used by a reserved
transport, without exposing its proof-valued smallness arguments. -/
theorem retainedReservedTransport_congr_owner
    {source target : Gaussian} {left right : Owner source}
    (same : left = right)
    (leftTargetNonzero rightTargetNonzero : target ≠ 0)
    (leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      left.track.initial.clearance.bound)
    (rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      right.track.initial.clearance.bound)
    (transportReserve retainedReserve : Coordinate) :
    retainedAtReserve
        (CCL.Riemann.ExactQuadraticOwnerClearance.reservedTransport left
          leftTargetNonzero leftSmall transportReserve) retainedReserve =
      retainedAtReserve
        (CCL.Riemann.ExactQuadraticOwnerClearance.reservedTransport right
          rightTargetNonzero rightSmall transportReserve) retainedReserve := by
  subst right
  rfl

/-- Reserve-triggered retention or reset preserves the root occurrence. -/
def retainedAtReserveRootEquivalent {parameter : Gaussian}
    (owner : Owner parameter) (reserve : Coordinate) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        owner.parameterNonzero owner)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        owner.parameterNonzero (retainedAtReserve owner reserve)) := by
  unfold retainedAtReserve
  by_cases enough : reserve <= owner.track.initial.clearance.bound
  · rw [if_pos enough]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  · rw [if_neg enough]
    exact recenteredRootEquivalent owner

/-- One requested next base point and the positive squared root diameter to
enforce before moving to it. -/
structure StepRequest where
  endpoint : Endpoint
  rootDiameter : Coordinate
  rootDiameterPositive : 0 < rootDiameter

/-- Clearance retained after an executable move.  Positivity is sufficient
because quadratic transport now refreshes exact side clearances after every
nontrivial move; a fresh preparation is requested only when that finite
presentation can no longer carry the occurrence. -/
def transportReserve {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : ClearSegment polynomial ambient start finish)
    (_left : Endpoint) (_request : StepRequest) : Coordinate :=
  0

/-- Convert a local unit-interval parameter on one requested edge back to
the original clear segment's parameter. -/
def parameterAt (left : Endpoint) (request : StepRequest)
    (fraction : Coordinate) : Coordinate :=
  if fraction = 0 then left.parameter
  else if fraction = 1 then request.endpoint.parameter
  else left.parameter + fraction *
    (request.endpoint.parameter - left.parameter)

/-- The endpoint-aware executable parameter map still agrees exactly with the
usual affine formula. -/
theorem parameterAt_eq_affine (left : Endpoint) (request : StepRequest)
    (fraction : Coordinate) :
    parameterAt left request fraction =
      left.parameter + fraction *
        (request.endpoint.parameter - left.parameter) := by
  unfold parameterAt
  split
  next atStart =>
    subst fraction
    ring1
  next notStart =>
    split
    next atFinish =>
      subst fraction
      ring1
    next notFinish => rfl

@[simp] theorem parameterAt_zero (left : Endpoint) (request : StepRequest) :
    parameterAt left request 0 = left.parameter := by
  unfold parameterAt
  rw [if_pos rfl]

@[simp] theorem parameterAt_one (left : Endpoint) (request : StepRequest) :
    parameterAt left request 1 = request.endpoint.parameter := by
  unfold parameterAt
  rw [if_neg (show (1 : Coordinate) ≠ 0 by decide), if_pos rfl]

theorem parameterAt_between (left : Endpoint) (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    left.parameter <= parameterAt left request fraction ∧
      parameterAt left request fraction <= request.endpoint.parameter := by
  rw [parameterAt_eq_affine]
  have edgeNonnegative :
      (0 : Coordinate) <= request.endpoint.parameter - left.parameter :=
    RFAP.ConstructiveFraction.sub_nonneg_direct ordered
  have localMoveNonnegative :
      0 <= fraction * (request.endpoint.parameter - left.parameter) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct localInside.1
      edgeNonnegative
  have remainingNonnegative :
      0 <= (1 - fraction) *
        (request.endpoint.parameter - left.parameter) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.sub_nonneg_direct localInside.2)
      edgeNonnegative
  constructor
  · exact le_add_of_nonneg_right localMoveNonnegative
  · calc
      left.parameter + fraction *
            (request.endpoint.parameter - left.parameter) <=
          (left.parameter + fraction *
              (request.endpoint.parameter - left.parameter)) +
            (1 - fraction) *
              (request.endpoint.parameter - left.parameter) :=
        le_add_of_nonneg_right remainingNonnegative
      _ = request.endpoint.parameter := by ring1

theorem parameterAt_inside (left : Endpoint) (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (0 : Coordinate) <= parameterAt left request fraction ∧
      parameterAt left request fraction <= 1 := by
  have between := parameterAt_between left request ordered fraction localInside
  exact ⟨left.inside.1.trans between.1,
    between.2.trans request.endpoint.inside.2⟩

theorem pointAt_parameterAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (request : StepRequest) (fraction : Coordinate) :
    segment.pointAt (parameterAt left request fraction) =
      (segment.restrict within left.parameter request.endpoint.parameter
        left.inside request.endpoint.inside).pointAt fraction := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [parameterAt_eq_affine,
      CCL.Riemann.BranchCuts.ClearSegment.pointAt,
      CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im] <;> ring1

/-- An inherited owner already has every quantitative property supplied by
uniform preparation.  Reusing such an owner avoids rebuilding the same small
quadratic box before every continuation edge. -/
def AlreadyPrepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) : Prop :=
  owner.track.initial.box.diagonalSq < request.rootDiameter ∧
    CCL.Riemann.UniformSquareRootPreparation.predictedClearance segment
        request.rootDiameter ≤ owner.track.initial.clearance.bound ∧
      owner.track.initial.box.Refines
        (CCL.Riemann.UniformSquareRootPreparation.rootAmbient segment)

instance alreadyPreparedDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) : Decidable (AlreadyPrepared segment current owner request) := by
  unfold AlreadyPrepared RFAP.Boxes.Box.Refines
  infer_instance

private def baselinePrepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    Owner (polynomial.eval (segment.pointAt current.parameter)) :=
  if AlreadyPrepared segment current owner request then
    if CCL.Riemann.ClearSheetContinuation.variationBound segment
        current.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound then
      owner
    else
      strengthenQuadraticOwner owner
  else
    strengthenQuadraticOwner
      (CCL.Riemann.UniformSquareRootPreparation.prepared segment
        current.parameter current.inside owner request.rootDiameter
          request.rootDiameterPositive)

private def preparedWithRetries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) : Nat ->
      Owner (polynomial.eval (segment.pointAt current.parameter))
  | 0 => baselinePrepared segment current owner request
  | retries + 1 =>
      let baseline := baselinePrepared segment current owner request
      if CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
            baseline.track.initial.clearance.bound then
        baseline
      else
        preparedWithRetries segment current (recentered owner) request retries

/-- Thirty-three exact retries let a coarse edge follow a moving quadratic window
without introducing an unbounded search into the executable checker. -/
private def preparationRetryCount : Nat := 33

/-- Reuse the inexpensive inherited preparation while it already carries the
current edge.  If that exact comparison fails, make a bounded sequence of
finite moving resets, stopping as soon as an operationally equivalent
replacement carries the edge. -/
@[irreducible] def prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    Owner (polynomial.eval (segment.pointAt current.parameter)) :=
  preparedWithRetries segment current owner request preparationRetryCount

/-- If the inherited owner already has the requested geometry and carries the
edge, preparation returns it immediately.  This is the inexpensive first
branch of the bounded search, exposed without unfolding the remaining retry
budget. -/
theorem prepared_eq_self_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (carries : CCL.Riemann.ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound) :
    prepared segment current owner request = owner := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have baselineEq :
      baselinePrepared segment current owner request = owner := by
    unfold baselinePrepared
    rw [if_pos ready, if_pos carries]
  have baselineCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current owner request).track.initial.clearance.bound := by
    rw [baselineEq]
    exact carries
  rw [if_pos baselineCarries, baselineEq]

/-- If an inherited owner already has the requested geometry, its old
clearance misses the edge, and one exact same-box strengthening carries it,
then the bounded preparation loop stops at that strengthened owner on its
first attempt.  Exposing this branch algebraically avoids reducing the opaque
strengthening cache or traversing the remaining retry budget. -/
theorem prepared_eq_strengthenQuadraticOwner_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (notCarries : ¬ CCL.Riemann.ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound)
    (strengthenedCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (strengthenQuadraticOwner owner).track.initial.clearance.bound) :
    prepared segment current owner request = strengthenQuadraticOwner owner := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have baselineEq :
      baselinePrepared segment current owner request =
        strengthenQuadraticOwner owner := by
    unfold baselinePrepared
    rw [if_pos ready, if_neg notCarries]
  have baselineCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current owner request).track.initial.clearance.bound := by
    rw [baselineEq]
    exact strengthenedCarries
  rw [if_pos baselineCarries, baselineEq]

/-- A carrying same-box strengthening proves that canonical preparation
carries the edge, whether the inherited clearance already suffices or the
strengthening branch is selected. -/
theorem variation_lt_prepared_of_ready_of_strengthenedCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (strengthenedCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (strengthenQuadraticOwner owner).track.initial.clearance.bound) :
    CCL.Riemann.ClearSheetContinuation.variationBound segment
        current.parameter request.endpoint.parameter <
      (prepared segment current owner request).track.initial.clearance.bound := by
  by_cases carries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact carries
  · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
      request ready carries strengthenedCarries]
    exact strengthenedCarries

/-- Under the same hypothesis, preparation keeps exactly the inherited box.
This exposes the stable datum needed by a following cached transport without
requiring callers to decide whether strengthening was necessary. -/
theorem prepared_initial_box_eq_of_ready_of_strengthenedCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (strengthenedCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (strengthenQuadraticOwner owner).track.initial.clearance.bound) :
    (prepared segment current owner request).track.initial.box =
      owner.track.initial.box := by
  by_cases carries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
  · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
      request ready carries strengthenedCarries,
      strengthenQuadraticOwner_initial_box]

/-- Under the inexpensive ready-owner hypotheses, preparation preserves the
finite boundary-to-ambient dominance invariant whether it reuses the owner or
selects same-box strengthening. -/
theorem prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (strengthenedCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (strengthenQuadraticOwner owner).track.initial.clearance.bound)
    (dominance : AmbientClearanceDominance owner) :
    AmbientClearanceDominance (prepared segment current owner request) := by
  by_cases carries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact dominance
  · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
      request ready carries strengthenedCarries]
    exact strengthenQuadraticOwner_ambientClearanceDominance_of owner dominance

/-- The compact quadratic Horner budget follows the same inexpensive
reuse-or-strengthen preparation branches. -/
theorem prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (strengthenedCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (strengthenQuadraticOwner owner).track.initial.clearance.bound)
    (budget : QuadraticAmbientBudget owner) :
    QuadraticAmbientBudget (prepared segment current owner request) := by
  by_cases carries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact budget
  · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
      request ready carries strengthenedCarries]
    exact strengthenQuadraticOwner_quadraticAmbientBudget owner budget

/-- A lower margin calculated from the accepted variation survives either
the reuse or same-box-strengthening branch of preparation. -/
theorem prepared_margin_lower_of_ready_of_strengthenedCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (strengthenedCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (strengthenQuadraticOwner owner).track.initial.clearance.bound)
    (floor displacement : Coordinate)
    (variationMargin : floor ≤
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter - displacement) :
    floor ≤ (prepared segment current owner request).track.initial.clearance.bound -
      displacement := by
  by_cases carries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact variationMargin.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct carries.le
        displacement)
  · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
      request ready carries strengthenedCarries]
    exact variationMargin.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct
        strengthenedCarries.le displacement)

/-- If the inherited same-box clearance and its exact strengthening both miss
an edge, but one certified moving recenter is already prepared and carries
the edge, the bounded retry loop stops at that recentered owner.  This branch
interface exposes two finite comparisons instead of asking elaboration to
reduce the remaining retry budget. -/
theorem prepared_eq_recentered_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (notCarries : ¬ CCL.Riemann.ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound)
    (strengthenedNotCarries :
      ¬ CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (strengthenQuadraticOwner owner).track.initial.clearance.bound)
    (recenteredReady : AlreadyPrepared segment current (recentered owner)
      request)
    (recenteredCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound) :
    prepared segment current owner request = recentered owner := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have firstBaselineEq :
      baselinePrepared segment current owner request =
        strengthenQuadraticOwner owner := by
    unfold baselinePrepared
    rw [if_pos ready, if_neg notCarries]
  have firstBaselineNotCarries :
      ¬ CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current owner request).track.initial.clearance.bound := by
    rw [firstBaselineEq]
    exact strengthenedNotCarries
  rw [if_neg firstBaselineNotCarries]
  have secondBaselineEq :
      baselinePrepared segment current (recentered owner) request =
        recentered owner := by
    unfold baselinePrepared
    rw [if_pos recenteredReady, if_pos recenteredCarries]
  have secondBaselineCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current (recentered owner)
          request).track.initial.clearance.bound := by
    rw [secondBaselineEq]
    exact recenteredCarries
  rw [show 32 = 31 + 1 by rfl, preparedWithRetries,
    if_pos secondBaselineCarries, secondBaselineEq]

/-- If the inherited presentation, its strengthening, and the first moving
reset all miss an edge, but the second moving reset is prepared and carries,
the bounded preparation loop stops at exactly that second reset.  Caching this
two-reset branch keeps concrete paths from elaborating the remaining retry
budget or recomputing either finite moving search. -/
theorem prepared_eq_recentered_twice_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (notCarries : ¬ CCL.Riemann.ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound)
    (strengthenedNotCarries :
      ¬ CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (strengthenQuadraticOwner owner).track.initial.clearance.bound)
    (firstReady : AlreadyPrepared segment current (recentered owner) request)
    (firstNotCarries :
      ¬ CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound)
    (firstStrengthenedNotCarries :
      ¬ CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (strengthenQuadraticOwner (recentered owner)).track.initial.clearance.bound)
    (secondReady : AlreadyPrepared segment current
      (recentered (recentered owner)) request)
    (secondCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered (recentered owner)).track.initial.clearance.bound) :
    prepared segment current owner request =
      recentered (recentered owner) := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have firstBaselineEq :
      baselinePrepared segment current owner request =
        strengthenQuadraticOwner owner := by
    unfold baselinePrepared
    rw [if_pos ready, if_neg notCarries]
  have firstBaselineNotCarries :
      ¬ CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current owner request).track.initial.clearance.bound := by
    rw [firstBaselineEq]
    exact strengthenedNotCarries
  rw [if_neg firstBaselineNotCarries, show 32 = 31 + 1 by rfl,
    preparedWithRetries]
  have secondBaselineEq :
      baselinePrepared segment current (recentered owner) request =
        strengthenQuadraticOwner (recentered owner) := by
    unfold baselinePrepared
    rw [if_pos firstReady, if_neg firstNotCarries]
  have secondBaselineNotCarries :
      ¬ CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current (recentered owner)
          request).track.initial.clearance.bound := by
    rw [secondBaselineEq]
    exact firstStrengthenedNotCarries
  rw [if_neg secondBaselineNotCarries, show 31 = 30 + 1 by rfl,
    preparedWithRetries]
  have thirdBaselineEq :
      baselinePrepared segment current (recentered (recentered owner))
          request = recentered (recentered owner) := by
    unfold baselinePrepared
    rw [if_pos secondReady, if_pos secondCarries]
  have thirdBaselineCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current (recentered (recentered owner))
          request).track.initial.clearance.bound := by
    rw [thirdBaselineEq]
    exact secondCarries
  rw [if_pos thirdBaselineCarries, thirdBaselineEq]

/-- One ready recenter which carries the displayed edge is enough to prove
that the canonical bounded preparation carries it.  No negative comparison
for the inherited or strengthened owner is required from callers: the proof
splits those two executable branches internally and uses the recenter only
when both miss. -/
theorem variation_lt_prepared_of_ready_of_recenteredCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (recenteredReady : AlreadyPrepared segment current (recentered owner)
      request)
    (recenteredCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound) :
    CCL.Riemann.ClearSheetContinuation.variationBound segment
        current.parameter request.endpoint.parameter <
      (prepared segment current owner request).track.initial.clearance.bound := by
  by_cases carries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact carries
  · by_cases strengthenedCarries :
        CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          (strengthenQuadraticOwner owner).track.initial.clearance.bound
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
        request ready carries strengthenedCarries]
      exact strengthenedCarries
    · rw [prepared_eq_recentered_of_ready segment current owner request ready
        carries strengthenedCarries recenteredReady recenteredCarries]
      exact recenteredCarries

/-- The ready moving-reset route also preserves boundary-to-ambient dominance.
The proof follows the same three finite branches as edge acceptance. -/
theorem prepared_ambientClearanceDominance_of_ready_of_recenteredCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (recenteredReady : AlreadyPrepared segment current (recentered owner)
      request)
    (recenteredCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound)
    (dominance : AmbientClearanceDominance owner) :
    AmbientClearanceDominance (prepared segment current owner request) := by
  by_cases carries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact dominance
  · by_cases strengthenedCarries :
        CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          (strengthenQuadraticOwner owner).track.initial.clearance.bound
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
        request ready carries strengthenedCarries]
      exact strengthenQuadraticOwner_ambientClearanceDominance_of owner dominance
    · rw [prepared_eq_recentered_of_ready segment current owner request ready
        carries strengthenedCarries recenteredReady recenteredCarries]
      exact recentered_ambientClearanceDominance owner dominance

/-- The moving-reset preparation route also retains a compact Horner budget:
the inherited branches use the source budget, while the reset branch uses
the explicitly cached replacement-box budget. -/
theorem prepared_quadraticAmbientBudget_of_ready_of_recenteredCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (recenteredReady : AlreadyPrepared segment current (recentered owner)
      request)
    (recenteredCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound)
    (budget : QuadraticAmbientBudget owner)
    (recenteredBudget : QuadraticAmbientBudget (recentered owner)) :
    QuadraticAmbientBudget (prepared segment current owner request) := by
  by_cases carries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact budget
  · by_cases strengthenedCarries :
        CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          (strengthenQuadraticOwner owner).track.initial.clearance.bound
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
        request ready carries strengthenedCarries]
      exact strengthenQuadraticOwner_quadraticAmbientBudget owner budget
    · rw [prepared_eq_recentered_of_ready segment current owner request ready
        carries strengthenedCarries recenteredReady recenteredCarries]
      exact recenteredBudget

/-- Margin counterpart of the ready moving-reset route.  If either inherited
presentation carries, the accepted variation supplies the margin; only the
actual reset branch consumes the displayed reset margin. -/
theorem prepared_margin_lower_of_ready_of_recenteredCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (recenteredReady : AlreadyPrepared segment current (recentered owner)
      request)
    (recenteredCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound)
    (floor displacement : Coordinate)
    (variationMargin : floor ≤
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter - displacement)
    (recenteredMargin : floor ≤
      (recentered owner).track.initial.clearance.bound - displacement) :
    floor ≤ (prepared segment current owner request).track.initial.clearance.bound -
      displacement := by
  by_cases carries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact variationMargin.trans
      (RFAP.ConstructiveFraction.sub_le_sub_right_direct carries.le
        displacement)
  · by_cases strengthenedCarries :
        CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          (strengthenQuadraticOwner owner).track.initial.clearance.bound
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
        request ready carries strengthenedCarries]
      exact variationMargin.trans
        (RFAP.ConstructiveFraction.sub_le_sub_right_direct
          strengthenedCarries.le displacement)
    · rw [prepared_eq_recentered_of_ready segment current owner request ready
        carries strengthenedCarries recenteredReady recenteredCarries]
      exact recenteredMargin

/-- The prepared source occurrence already evaluated while accepting one
edge.  Keeping it in the executable subdivision prevents every later model
query from rerunning the bounded preparation search.  The equality field
retains the canonical specification used by the existing proof interface. -/
structure CachedSource {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) where
  preparedOwner : Owner
    (polynomial.eval (segment.pointAt current.parameter))
  preparedOwner_eq : preparedOwner = prepared segment current owner request

namespace CachedSource

/-- The canonical prepared source, packaged once for persistent reuse. -/
def canonical {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) : CachedSource segment current owner request where
  preparedOwner := prepared segment current owner request
  preparedOwner_eq := rfl

/-- Every well-specified cached source is the canonical cache; only its
evaluated sharing behavior differs. -/
theorem eq_canonical {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest}
    (cached : CachedSource segment current owner request) :
    cached = canonical segment current owner request := by
  cases cached with
  | mk preparedOwner preparedOwner_eq =>
      cases preparedOwner_eq
      rfl

end CachedSource

private theorem baselinePrepared_initial_box_refines_rootAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    (baselinePrepared segment current owner request).track.initial.box.Refines
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient segment) := by
  unfold baselinePrepared
  by_cases ready : AlreadyPrepared segment current owner request
  · rw [if_pos ready]
    by_cases carries :
        CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound
    · rw [if_pos carries]
      exact ready.2.2
    · rw [if_neg carries, strengthenQuadraticOwner_initial_box]
      exact ready.2.2
  · rw [if_neg ready, strengthenQuadraticOwner_initial_box,
      CCL.Riemann.UniformSquareRootPreparation.prepared_initial_box]
    exact
      (CCL.Riemann.UniformSquareRootPreparation.restartInput segment
        current.parameter current.inside owner request.rootDiameter
          request.rootDiameterPositive).centeredBox_refines

/-- Every prepared source box lies in the path-wide root ambient, whether it
was reused directly or constructed by the uniform fallback. -/
theorem prepared_initial_box_refines_rootAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    (prepared segment current owner request).track.initial.box.Refines
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient segment) := by
  unfold prepared
  have retryRefines : forall (retries : Nat)
      (candidate : Owner
        (polynomial.eval (segment.pointAt current.parameter))),
      (preparedWithRetries segment current candidate request retries).track.initial.box.Refines
        (CCL.Riemann.UniformSquareRootPreparation.rootAmbient segment) := by
    intro retries
    induction retries with
    | zero =>
        intro candidate
        exact baselinePrepared_initial_box_refines_rootAmbient segment current
          candidate request
    | succ retries inductionHypothesis =>
        intro candidate
        simp only [preparedWithRetries]
        by_cases carries :
            CCL.Riemann.ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
              (baselinePrepared segment current candidate
                request).track.initial.clearance.bound
        · rw [if_pos carries]
          exact baselinePrepared_initial_box_refines_rootAmbient segment current
            candidate request
        · rw [if_neg carries]
          exact inductionHypothesis (recentered candidate)
  exact retryRefines preparationRetryCount owner

/-- Explicit Newton-data lower bound for the clearance of a prepared owner.
Unlike the actual extracted clearance, this expression is available before
the extraction result is inspected. -/
def preparedClearanceLower
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (_current : Endpoint) (request : StepRequest) : Coordinate :=
  CCL.Riemann.UniformSquareRootPreparation.predictedClearance segment
    request.rootDiameter

theorem preparedClearanceLower_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) :
    0 < preparedClearanceLower segment current request :=
  CCL.Riemann.UniformSquareRootPreparation.predictedClearance_positive segment
    request.rootDiameter request.rootDiameterPositive

/-- One positive preparation-clearance floor valid at every parameter and
for either sheet when a common root-diameter request is used. -/
def uniformPreparedClearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) : Coordinate :=
  min
    (CCL.Riemann.UniformSquareRootPreparation.predictedClearance segment
      rootDiameter)
    1

theorem uniformPreparedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < uniformPreparedClearanceFloor segment rootDiameter :=
  lt_min
    (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_positive
      segment rootDiameter rootDiameterPositive)
    (by decide)

theorem uniformPreparedClearanceFloor_le_predicted
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) :
    uniformPreparedClearanceFloor segment rootDiameter <=
      CCL.Riemann.UniformSquareRootPreparation.predictedClearance segment
        rootDiameter :=
  min_le_left _ _

theorem preparedClearanceLower_le
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    preparedClearanceLower segment current request ≤
      (prepared segment current owner request).track.initial.clearance.bound := by
  have baselineLower : forall
      (candidate : Owner
        (polynomial.eval (segment.pointAt current.parameter))),
      preparedClearanceLower segment current request ≤
        (baselinePrepared segment current candidate request).track.initial.clearance.bound := by
    intro candidate
    unfold baselinePrepared
    by_cases ready : AlreadyPrepared segment current candidate request
    · rw [if_pos ready]
      by_cases carries :
          CCL.Riemann.ClearSheetContinuation.variationBound segment
              current.parameter request.endpoint.parameter <
            candidate.track.initial.clearance.bound
      · rw [if_pos carries]
        exact ready.2.1
      · rw [if_neg carries]
        exact ready.2.1.trans (strengthenQuadraticOwner_clearance_le candidate)
    · rw [if_neg ready, preparedClearanceLower,
        ← CCL.Riemann.UniformSquareRootPreparation.prepared_clearance_bound
          segment current.parameter current.inside candidate request.rootDiameter
            request.rootDiameterPositive]
      exact strengthenQuadraticOwner_clearance_le _
  unfold prepared
  have retryLower : forall (retries : Nat)
      (candidate : Owner
        (polynomial.eval (segment.pointAt current.parameter))),
      preparedClearanceLower segment current request ≤
        (preparedWithRetries segment current candidate request
          retries).track.initial.clearance.bound := by
    intro retries
    induction retries with
    | zero =>
        intro candidate
        exact baselineLower candidate
    | succ retries inductionHypothesis =>
        intro candidate
        simp only [preparedWithRetries]
        by_cases carries :
            CCL.Riemann.ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
              (baselinePrepared segment current candidate
                request).track.initial.clearance.bound
        · rw [if_pos carries]
          exact baselineLower candidate
        · rw [if_neg carries]
          exact inductionHypothesis (recentered candidate)
  exact retryLower preparationRetryCount owner

/-- Productive name of the division-ready root of a prepared source owner. -/
def preparedRootName {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) : Named :=
  ((prepared segment left owner request).certificate
    (segment.pointAt_eval_ne_zero left.parameter left.inside)).value.name

/-- Every owner admits the certified zero-displacement move used by a local
parameter-zero query. -/
theorem samePointSmall {parameter : Gaussian} (owner : Owner parameter) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (parameter - parameter) <
      owner.track.initial.clearance.bound := by
  rw [RFAP.ConstructiveGaussian.Gaussian.sub_self,
    RFAP.ConstructiveGaussian.Gaussian.normSq_zero]
  exact owner.track.initial.clearance.positive

/-- Productive root name after the explicit zero-displacement move from a
prepared source owner. -/
def zeroMoveRootName {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) : Named :=
  let source := prepared segment left owner request
  let nonzero := segment.pointAt_eval_ne_zero left.parameter left.inside
  ((reservedTransport source nonzero (samePointSmall source)
    (transportReserve segment left request)).certificate nonzero).value.name

theorem prepared_diagonal_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    (prepared segment current owner request).track.initial.box.diagonalSq <
      request.rootDiameter := by
  have baselineSmall : forall
      (candidate : Owner
        (polynomial.eval (segment.pointAt current.parameter))),
      (baselinePrepared segment current candidate request).track.initial.box.diagonalSq <
        request.rootDiameter := by
    intro candidate
    unfold baselinePrepared
    by_cases ready : AlreadyPrepared segment current candidate request
    · rw [if_pos ready]
      by_cases carries :
          CCL.Riemann.ClearSheetContinuation.variationBound segment
              current.parameter request.endpoint.parameter <
            candidate.track.initial.clearance.bound
      · rw [if_pos carries]
        exact ready.1
      · rw [if_neg carries, strengthenQuadraticOwner_initial_box]
        exact ready.1
    · rw [if_neg ready, strengthenQuadraticOwner_initial_box]
      exact CCL.Riemann.UniformSquareRootPreparation.prepared_diagonal_lt segment
        current.parameter current.inside candidate request.rootDiameterPositive
  unfold prepared
  have retrySmall : forall (retries : Nat)
      (candidate : Owner
        (polynomial.eval (segment.pointAt current.parameter))),
      (preparedWithRetries segment current candidate request
        retries).track.initial.box.diagonalSq < request.rootDiameter := by
    intro retries
    induction retries with
    | zero =>
        intro candidate
        exact baselineSmall candidate
    | succ retries inductionHypothesis =>
        intro candidate
        simp only [preparedWithRetries]
        by_cases carries :
            CCL.Riemann.ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
              (baselinePrepared segment current candidate
                request).track.initial.clearance.bound
        · rw [if_pos carries]
          exact baselineSmall candidate
        · rw [if_neg carries]
          exact inductionHypothesis (recentered candidate)
  exact retrySmall preparationRetryCount owner

/-- The prepared source owner and its same-box direct endpoint transport. -/
def transported {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    Owner (polynomial.eval
      (segment.pointAt request.endpoint.parameter)) :=
  reservedTransport (prepared segment left owner request)
    (segment.pointAt_eval_ne_zero request.endpoint.parameter
      request.endpoint.inside)
    ((CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt small)
    (transportReserve segment left request)

/-- Productive name of the transported endpoint root before reconditioning. -/
def transportedRootName {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) : Named :=
  ((transported segment within left owner request small).certificate
    (segment.pointAt_eval_ne_zero request.endpoint.parameter
      request.endpoint.inside)).value.name

/-- Generic Newton transport and direct same-box transport name the same
target root occurrence. -/
def rootEquivalentOfDirectPresentation
    {source target : Gaussian} (sourceOwner : Owner source)
    (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceOwner.track.initial.clearance.bound)
    (result : Owner target)
    (relation : DirectPresentationRelation sourceOwner targetNonzero small
      result) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName targetNonzero
        (sourceOwner.advance targetNonzero small))
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName targetNonzero
        result) := by
  let tail := result.refineAt 1
  have tailStrictResult : tail.track.initial.box.StrictInterior
      result.track.initial.box := by
    change (CCL.Riemann.CoherentRoot.state result.track 1).box.StrictInterior
      result.track.initial.box
    exact CCL.Riemann.SquareRootTrackEquivalence.state_strict_initial_of_pos
      result.track (by decide)
  have tailStrictParent : tail.track.initial.box.StrictInterior
      relation.parent.track.initial.box :=
    tailStrictResult.trans_refines relation.resultRefinesParent
  have genericToParent :=
    (CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      targetNonzero relation.parent.track
        (sourceOwner.advance targetNonzero small).track
        relation.genericStrictParent).symm
  have parentToTail :=
    CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      targetNonzero relation.parent.track tail.track tailStrictParent
  have resultToTail :=
    CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      targetNonzero result.track tail.track tailStrictResult
  exact CCL.OperationalEquivalence.NamedEquivalent.trans genericToParent
    (CCL.OperationalEquivalence.NamedEquivalent.trans parentToTail
      resultToTail.symm)

/-- Generic Newton transport and direct same-box transport name the same
target root occurrence. -/
def directTransportRootEquivalentGeneric
    {source target : Gaussian} (sourceOwner : Owner source)
    (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceOwner.track.initial.clearance.bound) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName targetNonzero
        (sourceOwner.advance targetNonzero small))
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName targetNonzero
        (directTransport sourceOwner targetNonzero small)) := by
  rcases directTransport_generic_relation sourceOwner targetNonzero small with
      equal | strict
  · rw [equal]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  · exact rootEquivalentOfDirectPresentation sourceOwner targetNonzero small
      (directTransport sourceOwner targetNonzero small) strict

/-- Generic Newton transport and reserve-aware direct transport name the same
target root occurrence. -/
def reservedTransportRootEquivalentGeneric
    {source target : Gaussian} (sourceOwner : Owner source)
    (targetNonzero : target ≠ 0)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
      sourceOwner.track.initial.clearance.bound)
    (reserve : Coordinate) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName targetNonzero
        (sourceOwner.advance targetNonzero small))
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName targetNonzero
        (reservedTransport sourceOwner targetNonzero small reserve)) := by
  rcases reservedTransport_generic_relation sourceOwner targetNonzero small
      reserve with equal | strict
  · rw [equal]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  · exact rootEquivalentOfDirectPresentation sourceOwner targetNonzero small
      (reservedTransport sourceOwner targetNonzero small reserve) strict

/-- The productive name returned by reserved transport is independent of the
particular proof terms supplied for nonvanishing and smallness. -/
theorem reservedTransportRootName_proof_irrel
    {source target : Gaussian} (sourceOwner : Owner source)
    (firstNonzero secondNonzero : target ≠ 0)
    (firstSmall secondSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq (source - target) <
        sourceOwner.track.initial.clearance.bound)
    (reserve : Coordinate) :
    CCL.Riemann.SquareRootTrackEquivalence.ownerRootName firstNonzero
        (reservedTransport sourceOwner firstNonzero firstSmall reserve) =
      CCL.Riemann.SquareRootTrackEquivalence.ownerRootName secondNonzero
        (reservedTransport sourceOwner secondNonzero secondSmall reserve) := by
  have nonzero_eq : firstNonzero = secondNonzero :=
    Subsingleton.elim _ _
  cases nonzero_eq
  have small_eq : firstSmall = secondSmall := Subsingleton.elim _ _
  cases small_eq
  rfl

/-- The compact generic continuation name is operationally equivalent to the
direct endpoint owner used by an executable prepared edge. -/
def continuedRootNameEquivalentTransportedRootName
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        (prepared segment left owner request)
        ((CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
          within left.parameter request.endpoint.parameter left.inside
            request.endpoint.inside).trans_lt small))
      (transportedRootName segment within left owner request small) := by
  let source := prepared segment left owner request
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let normSmall :=
    (CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt small
  exact reservedTransportRootEquivalentGeneric source targetNonzero normSmall
    (transportReserve segment left request)

/-- The two displayed root anchors on an accepted edge are closer than the
requested source squared diameter. -/
theorem transported_anchor_distance_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((transported segment within left owner request small).track.initial.box.anchor -
          (prepared segment left owner request).track.initial.box.anchor) <
      request.rootDiameter := by
  let source := prepared segment left owner request
  let target := transported segment within left owner request small
  have refines : target.track.initial.box.Refines
      source.track.initial.box := by
    exact reservedTransport_initial_box_refines source
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside) _
      (transportReserve segment left request)
  exact (source.track.initial.box.normSq_sub_le_diagonalSq
    (refines.contains target.track.initial.box.contains_anchor)
    source.track.initial.box.contains_anchor).trans_lt
      (prepared_diagonal_lt segment left owner request)

/-- The ordinary interior point query before the two computational endpoint
shortcuts are applied. -/
def transportedInterior {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Owner (polynomial.eval
      (segment.pointAt (parameterAt left request fraction))) := by
  let parameter := parameterAt left request fraction
  have between := parameterAt_between left request ordered fraction localInside
  have localSmall :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          left.parameter parameter <
        (prepared segment left owner request).track.initial.clearance.bound :=
    (CCL.Riemann.ClearSheetContinuation.variationBound_le_of_between
      segment between.1 between.2).trans_lt small
  exact reservedTransport (prepared segment left owner request)
    (segment.pointAt_eval_ne_zero parameter
      (parameterAt_inside left request ordered fraction localInside))
    ((CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment within
      left.parameter parameter left.inside
        (parameterAt_inside left request ordered fraction localInside)).trans_lt
          localSmall)
    (transportReserve segment left request)

theorem transportedInterior_initial_box_refines
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (transportedInterior segment within left owner request ordered small
      fraction localInside).track.initial.box.Refines
        (prepared segment left owner request).track.initial.box := by
  let parameter := parameterAt left request fraction
  exact reservedTransport_initial_box_refines
    (prepared segment left owner request)
    (segment.pointAt_eval_ne_zero parameter
      (parameterAt_inside left request ordered fraction localInside)) _
    (transportReserve segment left request)

/-- A queried owner together with the finite witness that it remains in the
prepared source occurrence. -/
structure TransportedQuery (parameter : Gaussian) (source : Box) where
  owner : Owner parameter
  initial_box_refines : owner.track.initial.box.Refines source

/-- Construct both the point-query owner and its source-box witness.  Literal
endpoint queries use direct computational branches; interior queries retain
the ordinary affine Rouché transport. -/
def transportedQuery {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    TransportedQuery
      (polynomial.eval
        (segment.pointAt (parameterAt left request fraction)))
      (prepared segment left owner request).track.initial.box := by
  if atStart : fraction = 0 then
    subst fraction
    let queryOwner := reservedTransport (prepared segment left owner request)
      (segment.pointAt_eval_ne_zero left.parameter left.inside)
        (samePointSmall (prepared segment left owner request))
      (transportReserve segment left request)
    let query : TransportedQuery
        (polynomial.eval (segment.pointAt left.parameter))
        (prepared segment left owner request).track.initial.box :=
      { owner := queryOwner
        initial_box_refines :=
          reservedTransport_initial_box_refines
            (prepared segment left owner request)
            (segment.pointAt_eval_ne_zero left.parameter left.inside)
              (samePointSmall (prepared segment left owner request))
            (transportReserve segment left request) }
    simpa only [parameterAt_zero] using query
  else if atFinish : fraction = 1 then
    subst fraction
    let queryOwner := transported segment within left owner request small
    let query : TransportedQuery
        (polynomial.eval (segment.pointAt request.endpoint.parameter))
        (prepared segment left owner request).track.initial.box :=
      { owner := queryOwner
        initial_box_refines := by
          exact reservedTransport_initial_box_refines
            (prepared segment left owner request)
              (segment.pointAt_eval_ne_zero request.endpoint.parameter
                request.endpoint.inside) _
              (transportReserve segment left request) }
    simpa only [parameterAt_one] using query
  else
    exact
      { owner := transportedInterior segment within left owner request ordered
          small fraction localInside
        initial_box_refines := transportedInterior_initial_box_refines segment
          within left owner request ordered small fraction localInside }

/-- Transport the prepared source occurrence to any rational point of an
ordered accepted edge.  This is the productive, point-query form needed by a
uniform integration certificate. -/
def transportedAt {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Owner (polynomial.eval
      (segment.pointAt (parameterAt left request fraction))) :=
  (transportedQuery segment within left owner request ordered small fraction
    localInside).owner

/-- Variation proof for the direct query from the prepared left owner to one
local point of an accepted edge. -/
theorem pointVariationSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    CCL.Riemann.ClearSheetContinuation.variationBound segment left.parameter
        (parameterAt left request fraction) <
      (prepared segment left owner request).track.initial.clearance.bound :=
  (CCL.Riemann.ClearSheetContinuation.variationBound_le_of_between segment
    (parameterAt_between left request ordered fraction localInside).1
    (parameterAt_between left request ordered fraction localInside).2).trans_lt
      small

/-- Exact radicand-distance proof used by a direct local point query. -/
theorem pointNormSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval (segment.pointAt left.parameter) -
          polynomial.eval
            (segment.pointAt (parameterAt left request fraction))) <
      (prepared segment left owner request).track.initial.clearance.bound :=
  (CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment within
    left.parameter (parameterAt left request fraction) left.inside
      (parameterAt_inside left request ordered fraction localInside)).trans_lt
        (pointVariationSmall segment left owner request ordered small fraction
          localInside)

/-- Every endpoint-specialized point query is the same direct same-box
transport; the computational branches differ only in their proof terms. -/
theorem transportedAt_eq_directAdvance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    transportedAt segment within left owner request ordered small fraction
        localInside =
      reservedTransport (prepared segment left owner request)
        (segment.pointAt_eval_ne_zero (parameterAt left request fraction)
          (parameterAt_inside left request ordered fraction localInside))
        (pointNormSmall segment within left owner request ordered small fraction
          localInside)
        (transportReserve segment left request) := by
  unfold transportedAt transportedQuery
  by_cases atStart : fraction = 0
  · subst fraction
    rfl
  · rw [dif_neg atStart]
    by_cases atFinish : fraction = 1
    · subst fraction
      rfl
    · rw [dif_neg atFinish]
      rfl

/-- Every point-query owner remains nested in the one prepared source box.
This is the uniform same-sheet enclosure used by local differential models. -/
theorem transportedAt_initial_box_refines
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (transportedAt segment within left owner request ordered small
      fraction localInside).track.initial.box.Refines
        (prepared segment left owner request).track.initial.box := by
  exact (transportedQuery segment within left owner request ordered small
    fraction localInside).initial_box_refines

theorem transportedAt_anchor_distance_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((transportedAt segment within left owner request ordered small
          fraction localInside).track.initial.box.anchor -
          (prepared segment left owner request).track.initial.box.anchor) <
      request.rootDiameter := by
  let parameter := parameterAt left request fraction
  have between := parameterAt_between left request ordered fraction localInside
  have localSmall :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
          left.parameter parameter <
        (prepared segment left owner request).track.initial.clearance.bound :=
    (CCL.Riemann.ClearSheetContinuation.variationBound_le_of_between
      segment between.1 between.2).trans_lt small
  let source := prepared segment left owner request
  let target := transportedAt segment within left owner request ordered small
    fraction localInside
  have refines : target.track.initial.box.Refines
      source.track.initial.box := by
    exact transportedAt_initial_box_refines segment within left owner request
      ordered small fraction localInside
  exact (source.track.initial.box.normSq_sub_le_diagonalSq
    (refines.contains target.track.initial.box.contains_anchor)
    source.track.initial.box.contains_anchor).trans_lt
      (prepared_diagonal_lt segment left owner request)

/-- Retain the transported endpoint occurrence while it meets the uniform
prepared-clearance floor.  Only a loss of that reserve triggers the finite
quadratic overlap check and gentle moving reset. -/
def advance {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    Owner (polynomial.eval
      (segment.pointAt request.endpoint.parameter)) :=
  retainedAtReserve (transported segment within left owner request small)
    (preparedClearanceLower segment left request)

/-- Advance from the prepared source already stored on an accepted edge.
This is the executable counterpart of `advance`: it prevents the recursive
checker from rerunning the bounded preparation search immediately after that
same source was evaluated for the acceptance comparison. -/
def advanceCached {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound) :
    Owner (polynomial.eval
      (segment.pointAt request.endpoint.parameter)) :=
  retainedAtReserve
    (reservedTransport cached.preparedOwner
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      ((CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
        within left.parameter request.endpoint.parameter left.inside
          request.endpoint.inside).trans_lt small)
      (transportReserve segment left request))
    (preparedClearanceLower segment left request)

/-- The cached executable advance is exactly the canonical advance.  At
runtime the proof-only cast through this equality is erased, while the cached
owner value remains shared. -/
theorem advanceCached_eq_advance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    advanceCached segment within left owner request cached cachedSmall =
      advance segment within left owner request canonicalSmall := by
  cases cached with
  | mk preparedOwner preparedOwner_eq =>
      cases preparedOwner_eq
      rfl

/-- If the uniform predicted preparation floor fits under the transported
quadratic floor, the endpoint owner is retained verbatim and the moving-reset
search is not evaluated. -/
theorem advanceCached_eq_reservedTransport_of_quadraticCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (transportCache : QuadraticAmbientTransportCache cached.preparedOwner
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      ((CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
        within left.parameter request.endpoint.parameter left.inside
          request.endpoint.inside).trans_lt cachedSmall))
    (derivativeMarginLe :
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment ≤
        (1 / 4 : Coordinate)) :
    advanceCached segment within left owner request cached cachedSmall =
      reservedTransport cached.preparedOwner
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        ((CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
          within left.parameter request.endpoint.parameter left.inside
            request.endpoint.inside).trans_lt cachedSmall) 0 := by
  unfold advanceCached transportReserve
  apply retainedAtReserve_eq_self
  unfold preparedClearanceLower
  exact
    (CCL.Riemann.UniformSquareRootPreparation.predictedClearance_le_transportFloor
      segment request.rootDiameter request.rootDiameterPositive
        derivativeMarginLe).trans transportCache.clearanceFloor

/-- Exact rational successor data for an inexpensive ambient transport.  The
displayed side and boundary bounds are parameters of the cache, so explicit
examples can reduce each later edge check to rewriting cached data followed
by a small rational decision. -/
structure ExactAmbientAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (leftBound rightBound bottomBound topBound clearanceBound : Coordinate) :
    Prop where
  initialBox :
    (advanceCached segment within left owner request cached
      cachedSmall).track.initial.box = cached.preparedOwner.track.initial.box
  ambientBox :
    (advanceCached segment within left owner request cached
      cachedSmall).ambient = cached.preparedOwner.ambient
  ambientLeftBound :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientLeftClearance.bound = leftBound
  ambientRightBound :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientRightClearance.bound = rightBound
  ambientBottomBound :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientBottomClearance.bound = bottomBound
  ambientTopBound :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientTopClearance.bound = topBound
  clearanceBound :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.clearance.bound = clearanceBound
  dominance : AmbientClearanceDominance
    (advanceCached segment within left owner request cached cachedSmall)
  budget : QuadraticAmbientBudget
    (advanceCached segment within left owner request cached cachedSmall)

/-- Build an exact successor cache from one already-selected ambient transport
branch.  This theorem deliberately assumes the five rational evaluations as
data: it avoids imposing a coarse universal residual margin on worked
examples whose valid clearances vary substantially along a path. -/
theorem exactAmbientAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    {leftSmall : RFAP.ConstructiveGaussian.Gaussian.normSq
      (polynomial.eval (segment.pointAt left.parameter) -
        polynomial.eval (segment.pointAt request.endpoint.parameter)) <
      cached.preparedOwner.track.initial.ambientLeftClearance.bound}
    {rightSmall : RFAP.ConstructiveGaussian.Gaussian.normSq
      (polynomial.eval (segment.pointAt left.parameter) -
        polynomial.eval (segment.pointAt request.endpoint.parameter)) <
      cached.preparedOwner.track.initial.ambientRightClearance.bound}
    {bottomSmall : RFAP.ConstructiveGaussian.Gaussian.normSq
      (polynomial.eval (segment.pointAt left.parameter) -
        polynomial.eval (segment.pointAt request.endpoint.parameter)) <
      cached.preparedOwner.track.initial.ambientBottomClearance.bound}
    {topSmall : RFAP.ConstructiveGaussian.Gaussian.normSq
      (polynomial.eval (segment.pointAt left.parameter) -
        polynomial.eval (segment.pointAt request.endpoint.parameter)) <
      cached.preparedOwner.track.initial.ambientTopClearance.bound}
    (transportCache : AmbientReservedTransportCache cached.preparedOwner
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      ((CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
        within left.parameter request.endpoint.parameter left.inside
          request.endpoint.inside).trans_lt cachedSmall)
      0 leftSmall rightSmall bottomSmall topSmall)
    (leftBound rightBound bottomBound topBound clearanceBound : Coordinate)
    (leftBoundEq :
      (ambientLeftAfterMove cached.preparedOwner leftSmall).bound = leftBound)
    (rightBoundEq :
      (ambientRightAfterMove cached.preparedOwner rightSmall).bound = rightBound)
    (bottomBoundEq :
      (ambientBottomAfterMove cached.preparedOwner bottomSmall).bound =
        bottomBound)
    (topBoundEq :
      (ambientTopAfterMove cached.preparedOwner topSmall).bound = topBound)
    (clearanceBoundEq :
      min leftBound (min rightBound (min bottomBound topBound)) =
        clearanceBound)
    (retained : preparedClearanceLower segment left request ≤ clearanceBound)
    (budget : QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : RFAP.ConstructiveGaussian.Gaussian.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ExactAmbientAdvanceCache segment within left owner request cached
      cachedSmall leftBound rightBound bottomBound topBound clearanceBound := by
  have advanceEq :
      advanceCached segment within left owner request cached cachedSmall =
        reservedTransport cached.preparedOwner
          (segment.pointAt_eval_ne_zero request.endpoint.parameter
            request.endpoint.inside)
          ((CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
            within left.parameter request.endpoint.parameter left.inside
              request.endpoint.inside).trans_lt cachedSmall) 0 := by
    unfold advanceCached transportReserve
    apply retainedAtReserve_eq_self
    calc
      preparedClearanceLower segment left request ≤ clearanceBound := retained
      _ = min leftBound (min rightBound (min bottomBound topBound)) :=
        clearanceBoundEq.symm
      _ = min (ambientLeftAfterMove cached.preparedOwner leftSmall).bound
          (min (ambientRightAfterMove cached.preparedOwner rightSmall).bound
            (min
              (ambientBottomAfterMove cached.preparedOwner bottomSmall).bound
              (ambientTopAfterMove cached.preparedOwner topSmall).bound)) := by
        rw [leftBoundEq, rightBoundEq, bottomBoundEq, topBoundEq]
      _ = (reservedTransport cached.preparedOwner
          (segment.pointAt_eval_ne_zero request.endpoint.parameter
            request.endpoint.inside)
          ((CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
            within left.parameter request.endpoint.parameter left.inside
              request.endpoint.inside).trans_lt cachedSmall)
          0).track.initial.clearance.bound := transportCache.clearanceBound.symm
  refine
    { initialBox := ?_
      ambientBox := ?_
      ambientLeftBound := ?_
      ambientRightBound := ?_
      ambientBottomBound := ?_
      ambientTopBound := ?_
      clearanceBound := ?_
      dominance := ?_
      budget := ?_ }
  · rw [advanceEq]
    exact transportCache.initialBox
  · rw [advanceEq]
    exact transportCache.ambientBox
  · rw [advanceEq, transportCache.ambientLeftBound]
    exact leftBoundEq
  · rw [advanceEq, transportCache.ambientRightBound]
    exact rightBoundEq
  · rw [advanceEq, transportCache.ambientBottomBound]
    exact bottomBoundEq
  · rw [advanceEq, transportCache.ambientTopBound]
    exact topBoundEq
  · rw [advanceEq, transportCache.clearanceBound, leftBoundEq, rightBoundEq,
      bottomBoundEq, topBoundEq]
    exact clearanceBoundEq
  · rw [advanceEq]
    exact transportCache.ambientClearanceDominance
  · rw [advanceEq]
    refine
      { parameterNormSqLe := targetNormSqLe
        verticalIntervalSqLe := ?_
        horizontalIntervalSqLe := ?_
        leftNonzero := ?_
        rightNonzero := ?_
        bottomNonzero := ?_
        topNonzero := ?_
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [transportCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [transportCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [transportCache.initialBox]
      exact budget.leftNonzero
    · rw [transportCache.initialBox]
      exact budget.rightNonzero
    · rw [transportCache.initialBox]
      exact budget.bottomNonzero
    · rw [transportCache.initialBox]
      exact budget.topNonzero
    · rw [transportCache.initialBox]
      exact budget.leftSqLe
    · rw [transportCache.initialBox]
      exact budget.rightSqLe
    · rw [transportCache.initialBox]
      exact budget.bottomSqLe
    · rw [transportCache.initialBox]
      exact budget.topSqLe

/-- Stable successor facts at an explicit positive residual margin.  This is
the reusable cache for paths whose valid margin is smaller than the older
uniform half-unit specialization. -/
structure ParametricQuadraticAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (marginFloor : Coordinate) : Prop where
  initialBox :
    (advanceCached segment within left owner request cached
      cachedSmall).track.initial.box = cached.preparedOwner.track.initial.box
  ambientBox :
    (advanceCached segment within left owner request cached
      cachedSmall).ambient = cached.preparedOwner.ambient
  clearanceFloor :
    quadraticAmbientTransportFloorAt marginFloor ≤
      (advanceCached segment within left owner request cached
        cachedSmall).track.initial.clearance.bound
  ambientLeftQuarterSq :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientLeftClearance.bound ≤
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  clearanceQuarterSq :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.clearance.bound ≤
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  dominance : AmbientClearanceDominance
    (advanceCached segment within left owner request cached cachedSmall)
  budget : QuadraticAmbientBudget
    (advanceCached segment within left owner request cached cachedSmall)

/-- Construct a retained successor at an arbitrary cached positive margin.
The explicit `predictedLeFloor` premise keeps the preparation estimate local
to the concrete segment instead of forcing a globally coarse comparison. -/
theorem parametricQuadraticAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (marginFloor : Coordinate) (marginFloorPositive : 0 < marginFloor)
    (predictedLeFloor : preparedClearanceLower segment left request ≤
      quadraticAmbientTransportFloorAt marginFloor)
    (dominance : AmbientClearanceDominance cached.preparedOwner)
    (marginLower : marginFloor ≤
      cached.preparedOwner.track.initial.clearance.bound -
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (budget : QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : RFAP.ConstructiveGaussian.Gaussian.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricQuadraticAdvanceCache segment within left owner request cached
      cachedSmall marginFloor := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let moveSmall :=
    (CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt cachedSmall
  let transportCache :=
    CCL.Riemann.ExactQuadraticOwnerClearance.parametricQuadraticAmbientTransportCache
      cached.preparedOwner targetNonzero moveSmall different dominance
        marginFloor marginFloorPositive marginLower budget targetNormSqLe
  have advanceEq :
      advanceCached segment within left owner request cached cachedSmall =
        reservedTransport cached.preparedOwner targetNonzero moveSmall 0 := by
    unfold advanceCached transportReserve
    apply retainedAtReserve_eq_self
    exact predictedLeFloor.trans transportCache.clearanceFloor
  refine
    { initialBox := ?_
      ambientBox := ?_
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ?_
      budget := ?_ }
  · rw [advanceEq]
    exact transportCache.initialBox
  · rw [advanceEq]
    exact transportCache.ambientBox
  · rw [advanceEq]
    exact transportCache.clearanceFloor
  · rw [advanceEq]
    exact transportCache.ambientLeftQuarterSq
  · rw [advanceEq]
    exact transportCache.clearanceQuarterSq
  · rw [advanceEq]
    exact transportCache.dominance
  · rw [advanceEq]
    exact transportCache.budget

/-- One cached same-box preparation and transport step at an explicit
residual margin.  The record retains precisely the state needed to iterate
the construction without reopening either finite search. -/
structure ParametricSameBoxStep
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box)
    (directLower preparedUpper marginFloor : Coordinate) : Prop where
  ready : AlreadyPrepared segment left owner request
  strengthenedCarries :
    CCL.Riemann.ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter <
      (strengthenQuadraticOwner owner).track.initial.clearance.bound
  canonicalSmall :
    CCL.Riemann.ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter <
      (prepared segment left owner request).track.initial.clearance.bound
  preparedAmbientLeftLe :
    (CachedSource.canonical segment left owner request).preparedOwner.track.initial.ambientLeftClearance.bound ≤
      preparedUpper
  advanceCache : ParametricQuadraticAdvanceCache segment within left owner
    request (CachedSource.canonical segment left owner request) canonicalSmall
      marginFloor
  nextOwnerBox :
    (advanceCached segment within left owner request
      (CachedSource.canonical segment left owner request)
        canonicalSmall).track.initial.box = box
  nextAmbientLeftLeQuarter :
    (advanceCached segment within left owner request
      (CachedSource.canonical segment left owner request)
        canonicalSmall).track.initial.ambientLeftClearance.bound ≤
      preparedUpper ^ 2 / 4

/-- Construct the reusable same-box step from cached direct resultant bounds
and two small rational floor comparisons. -/
theorem parametricSameBoxStep
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box)
    (boxEq : owner.track.initial.box = box)
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (CCL.Riemann.UniformSquareRootPreparation.rootAmbient segment))
    (currentFloor : Coordinate)
    (predictedLeCurrent :
      preparedClearanceLower segment left request ≤ currentFloor)
    (currentFloorLe : currentFloor ≤ owner.track.initial.clearance.bound)
    (dominance : AmbientClearanceDominance owner)
    (budget : QuadraticAmbientBudget owner)
    (directLower preparedUpper : Coordinate)
    (ownerAmbientLeftLe :
      owner.track.initial.ambientLeftClearance.bound ≤ preparedUpper)
    (directCache : DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      CCL.Riemann.ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (marginFloor : Coordinate) (marginFloorPositive : 0 < marginFloor)
    (predictedLeTransportFloor :
      preparedClearanceLower segment left request ≤
        quadraticAmbientTransportFloorAt marginFloor)
    (variationMargin : marginFloor ≤
      CCL.Riemann.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (targetNormSqLe : RFAP.ConstructiveGaussian.Gaussian.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper marginFloor := by
  have ready : AlreadyPrepared segment left owner request :=
    ⟨boxEq ▸ boxSmall, predictedLeCurrent.trans currentFloorLe,
      boxEq ▸ boxRefines⟩
  let actualCache : DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter))
      owner.track.initial.box directLower preparedUpper := by
    rw [boxEq]
    exact directCache
  have strengthenedCarries :
      CCL.Riemann.ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (strengthenQuadraticOwner owner).track.initial.clearance.bound :=
    (variationLtDirectLower.trans_le actualCache.lower_le).trans_le
      (directBoundaryClearance_le_strengthenQuadraticOwner owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero)
  have canonicalSmall :=
    variation_lt_prepared_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries
  let cached := CachedSource.canonical segment left owner request
  have preparedDominance : AmbientClearanceDominance cached.preparedOwner :=
    prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries dominance
  have preparedBudget : QuadraticAmbientBudget cached.preparedOwner :=
    prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries budget
  have preparedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        preparedUpper := by
    change (prepared segment left owner request).track.initial.ambientLeftClearance.bound ≤
      preparedUpper
    by_cases carries :
        CCL.Riemann.ClearSheetContinuation.variationBound segment
            left.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound
    · rw [prepared_eq_self_of_ready segment left owner request ready carries]
      exact ownerAmbientLeftLe
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment left owner
        request ready carries strengthenedCarries]
      rcases strengthenQuadraticOwner_ambient_clearance_eq owner
          actualCache.leftNonzero actualCache.rightNonzero
            actualCache.bottomNonzero actualCache.topNonzero with
        ⟨leftEq, _rightEq, _bottomEq, _topEq⟩
      rw [leftEq, strengthenQuadraticOwner_clearance_eq_max owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero]
      exact max_le (dominance.left.trans ownerAmbientLeftLe)
        actualCache.le_upper
  have preparedMargin : marginFloor ≤
      cached.preparedOwner.track.initial.clearance.bound -
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) :=
    prepared_margin_lower_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries marginFloor _ variationMargin
  have advanceCache : ParametricQuadraticAdvanceCache segment within left owner
      request cached canonicalSmall marginFloor := by
    apply parametricQuadraticAdvanceCache segment within left owner request
      cached canonicalSmall different marginFloor marginFloorPositive
        predictedLeTransportFloor preparedDominance preparedMargin
          preparedBudget targetNormSqLe
  have nextOwnerBox :
      (advanceCached segment within left owner request cached
        canonicalSmall).track.initial.box = box := by
    calc
      (advanceCached segment within left owner request cached
          canonicalSmall).track.initial.box =
          cached.preparedOwner.track.initial.box := advanceCache.initialBox
      _ = owner.track.initial.box :=
        prepared_initial_box_eq_of_ready_of_strengthenedCarries segment left
          owner request ready strengthenedCarries
      _ = box := boxEq
  have preparedSquareLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 ≤
        preparedUpper ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
        preparedAmbientLeftLe 2
  have quarterSquareLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        preparedUpper ^ 2 / 4 := by
    change
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
          (4 : Coordinate)⁻¹ ≤
        preparedUpper ^ 2 * (4 : Coordinate)⁻¹
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      preparedSquareLe
        (RFAP.ConstructiveFraction.inv_pos_direct (by decide)).le
  have nextAmbientLeftLeQuarter :=
    advanceCache.ambientLeftQuarterSq.trans quarterSquareLe
  exact ⟨ready, strengthenedCarries, canonicalSmall, preparedAmbientLeftLe,
    advanceCache, nextOwnerBox, nextAmbientLeftLeQuarter⟩

/-- The stable facts needed by the next explicit prepared edge, cached after
retention has hidden the raw `reservedTransport` term. -/
structure QuadraticAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound) : Prop where
  initialBox :
    (advanceCached segment within left owner request cached
      cachedSmall).track.initial.box = cached.preparedOwner.track.initial.box
  ambientBox :
    (advanceCached segment within left owner request cached
      cachedSmall).ambient = cached.preparedOwner.ambient
  clearanceFloor : quadraticAmbientTransportFloor ≤
    (advanceCached segment within left owner request cached
      cachedSmall).track.initial.clearance.bound
  ambientLeftQuarterSq :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientLeftClearance.bound ≤
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  clearanceQuarterSq :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.clearance.bound ≤
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  dominance : AmbientClearanceDominance
    (advanceCached segment within left owner request cached cachedSmall)
  budget : QuadraticAmbientBudget
    (advanceCached segment within left owner request cached cachedSmall)

/-- Construct all stable successor facts from one explicit prepared-source
margin calculation. -/
theorem quadraticAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (derivativeMarginLe :
      CCL.Riemann.ClearSheetContinuation.squareRootDerivativeMargin segment ≤
        (1 / 4 : Coordinate))
    (dominance : AmbientClearanceDominance cached.preparedOwner)
    (marginLower : (1 : Coordinate) / 2 ≤
      cached.preparedOwner.track.initial.clearance.bound -
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (budget : QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : RFAP.ConstructiveGaussian.Gaussian.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    QuadraticAdvanceCache segment within left owner request cached
      cachedSmall := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let moveSmall :=
    (CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt cachedSmall
  let transportCache :=
    CCL.Riemann.ExactQuadraticOwnerClearance.quadraticAmbientTransportCache
      cached.preparedOwner targetNonzero moveSmall different dominance
        marginLower budget targetNormSqLe
  have advanceEq :=
    advanceCached_eq_reservedTransport_of_quadraticCache segment within left
      owner request cached cachedSmall transportCache derivativeMarginLe
  refine
    { initialBox := ?_
      ambientBox := ?_
      clearanceFloor := ?_
      ambientLeftQuarterSq := ?_
      clearanceQuarterSq := ?_
      dominance := ?_
      budget := ?_ }
  · rw [advanceEq]
    exact transportCache.initialBox
  · rw [advanceEq]
    exact transportCache.ambientBox
  · rw [advanceEq]
    exact transportCache.clearanceFloor
  · rw [advanceEq]
    exact transportCache.ambientLeftQuarterSq
  · rw [advanceEq]
    exact transportCache.clearanceQuarterSq
  · rw [advanceEq]
    exact transportCache.dominance
  · rw [advanceEq]
    exact transportCache.budget

/-- The finite same-occurrence bridge used by the endpoint reset. -/
def stepBridge {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    CCL.Riemann.SquareRootReconditioning.Bridge
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      (transported segment within left owner request small) :=
  CCL.Riemann.SquareRootReconditioning.bridge
    (segment.pointAt_eval_ne_zero request.endpoint.parameter
      request.endpoint.inside)
    (transported segment within left owner request small)

/-- Preparing the source owner does not change its division-ready square
root. -/
def sourceRootEquivalent {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) :
    NamedEquivalent
      (owner.certificate
        (segment.pointAt_eval_ne_zero left.parameter left.inside)).value.name
      ((prepared segment left owner request).certificate
        (segment.pointAt_eval_ne_zero left.parameter left.inside)).value.name := by
  have baselineEquivalent : forall
      (candidate : Owner
        (polynomial.eval (segment.pointAt left.parameter))),
      NamedEquivalent
        (candidate.certificate
          (segment.pointAt_eval_ne_zero left.parameter left.inside)).value.name
        ((baselinePrepared segment left candidate request).certificate
          (segment.pointAt_eval_ne_zero left.parameter left.inside)).value.name := by
    intro candidate
    let common := CCL.Riemann.UniformSquareRootPreparation.bridgeTrack segment
      left.parameter left.inside candidate request.rootDiameter
        request.rootDiameterPositive
    have oldToCommon :=
      CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
        (segment.pointAt_eval_ne_zero left.parameter left.inside) candidate.track
          common
        (CCL.Riemann.UniformSquareRootPreparation.bridgeTrack_initial_strict_owner
          segment left.parameter left.inside candidate
            request.rootDiameterPositive)
    have preparedToCommon :=
      CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
        (segment.pointAt_eval_ne_zero left.parameter left.inside)
          (baselinePrepared segment left candidate request).track common (by
            unfold baselinePrepared
            by_cases ready : AlreadyPrepared segment left candidate request
            · rw [if_pos ready]
              by_cases carries :
                  CCL.Riemann.ClearSheetContinuation.variationBound segment
                      left.parameter request.endpoint.parameter <
                    candidate.track.initial.clearance.bound
              · rw [if_pos carries]
                exact
                  CCL.Riemann.UniformSquareRootPreparation.bridgeTrack_initial_strict_owner
                    segment left.parameter left.inside candidate
                      request.rootDiameterPositive
              · rw [if_neg carries, strengthenQuadraticOwner_initial_box]
                exact
                  CCL.Riemann.UniformSquareRootPreparation.bridgeTrack_initial_strict_owner
                    segment left.parameter left.inside candidate
                      request.rootDiameterPositive
            · rw [if_neg ready, strengthenQuadraticOwner_initial_box]
              exact
                CCL.Riemann.UniformSquareRootPreparation.bridgeTrack_initial_strict_prepared
                  segment left.parameter left.inside candidate
                    request.rootDiameterPositive)
    exact CCL.OperationalEquivalence.NamedEquivalent.trans oldToCommon
      preparedToCommon.symm
  have retryEquivalent : forall (retries : Nat)
      (candidate : Owner
        (polynomial.eval (segment.pointAt left.parameter))),
      NamedEquivalent
        (candidate.certificate
          (segment.pointAt_eval_ne_zero left.parameter left.inside)).value.name
        ((preparedWithRetries segment left candidate request
          retries).certificate
            (segment.pointAt_eval_ne_zero left.parameter left.inside)).value.name := by
    intro retries
    induction retries with
    | zero =>
        intro candidate
        exact baselineEquivalent candidate
    | succ retries inductionHypothesis =>
        intro candidate
        simp only [preparedWithRetries]
        by_cases carries :
            CCL.Riemann.ClearSheetContinuation.variationBound segment
                left.parameter request.endpoint.parameter <
              (baselinePrepared segment left candidate
                request).track.initial.clearance.bound
        · rw [if_pos carries]
          exact baselineEquivalent candidate
        · rw [if_neg carries]
          have reset : NamedEquivalent
              (candidate.certificate
                (segment.pointAt_eval_ne_zero left.parameter
                  left.inside)).value.name
              ((recentered candidate).certificate
                (segment.pointAt_eval_ne_zero left.parameter
                  left.inside)).value.name := by
            simpa only
                [CCL.Riemann.SquareRootTrackEquivalence.ownerRootName] using
              recenteredRootEquivalent candidate
          exact CCL.OperationalEquivalence.NamedEquivalent.trans reset
            (inductionHypothesis (recentered candidate))
  unfold prepared
  exact retryEquivalent preparationRetryCount owner

/-! ## Congruent continuation from equivalent prepared occurrences -/

/-- Seven rational variation comparisons sufficient to continue two
operationally equal source occurrences to the same target occurrence.  The
extra five checks cover their canonical reconditionings and explicit common
bridge tails. -/
structure VariationCongruenceSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))) : Prop where
  firstSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
    left.parameter right.parameter < first.track.initial.clearance.bound
  secondSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
    left.parameter right.parameter < second.track.initial.clearance.bound
  firstFresh : CCL.Riemann.ClearSheetContinuation.variationBound segment
    left.parameter right.parameter <
      CCL.Riemann.SquareRootTrackEquivalence.freshSourceClearance
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first
  secondFresh : CCL.Riemann.ClearSheetContinuation.variationBound segment
    left.parameter right.parameter <
      CCL.Riemann.SquareRootTrackEquivalence.freshSourceClearance
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second
  firstBridge : CCL.Riemann.ClearSheetContinuation.variationBound segment
    left.parameter right.parameter <
      CCL.Riemann.SquareRootTrackEquivalence.bridgeTailClearance
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first
  secondBridge : CCL.Riemann.ClearSheetContinuation.variationBound segment
    left.parameter right.parameter <
      CCL.Riemann.SquareRootTrackEquivalence.bridgeTailClearance
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second
  freshCommon : CCL.Riemann.ClearSheetContinuation.variationBound segment
    left.parameter right.parameter <
      CCL.Riemann.SquareRootTrackEquivalence.freshCommonClearance
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first

namespace VariationCongruenceSmall

/-- The dense-Horner variation theorem turns the seven mesh comparisons into
the exact radicand-distance certificate consumed by continuation congruence. -/
theorem toContinuationCongruenceSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    (within : segment.WithinAmbient)
    {left right : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (small : VariationCongruenceSmall segment left right first second) :
    CCL.Riemann.SquareRootTrackEquivalence.ContinuationCongruenceSmall
      (segment.pointAt_eval_ne_zero left.parameter left.inside) first second
      (polynomial.eval (segment.pointAt right.parameter)) := by
  have variation :=
    CCL.Riemann.ClearSheetContinuation.evaluation_variation_le segment within
      left.parameter right.parameter left.inside right.inside
  exact
    { firstSmall := variation.trans_lt small.firstSmall
      secondSmall := variation.trans_lt small.secondSmall
      firstFresh := variation.trans_lt small.firstFresh
      secondFresh := variation.trans_lt small.secondFresh
      firstBridge := variation.trans_lt small.firstBridge
      secondBridge := variation.trans_lt small.secondBridge
      freshCommon := variation.trans_lt small.freshCommon }

end VariationCongruenceSmall

/-- General common-target form of prepared continuation congruence.  The two
source preparations may use different diameter requests, and the target may
be any displayed endpoint whose variation satisfies the finite certificate. -/
def preparedContinuationAtRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (firstRequest secondRequest : StepRequest)
    (target : Endpoint)
    (sourceEquivalent : NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second))
    (small : VariationCongruenceSmall segment left target
      (prepared segment left first firstRequest)
      (prepared segment left second secondRequest)) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero target.parameter target.inside)
        (prepared segment left first firstRequest)
        (small.toContinuationCongruenceSmall within).firstSmall)
      (CCL.Riemann.SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero target.parameter target.inside)
        (prepared segment left second secondRequest)
        (small.toContinuationCongruenceSmall within).secondSmall) := by
  let sourceNonzero := segment.pointAt_eval_ne_zero left.parameter left.inside
  let firstPrepared := prepared segment left first firstRequest
  let secondPrepared := prepared segment left second secondRequest
  have firstPreparation := sourceRootEquivalent segment left first firstRequest
  have secondPreparation := sourceRootEquivalent segment left second
    secondRequest
  have preparedEquivalent : NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName sourceNonzero
        firstPrepared)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName sourceNonzero
        secondPrepared) := by
    exact CCL.OperationalEquivalence.NamedEquivalent.trans
      firstPreparation.symm
        (CCL.OperationalEquivalence.NamedEquivalent.trans sourceEquivalent
          secondPreparation)
  exact
    CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_continued_of_rootEquivalent
      sourceNonzero
      (segment.pointAt_eval_ne_zero target.parameter target.inside)
      firstPrepared secondPrepared preparedEquivalent
        (small.toContinuationCongruenceSmall within)

/-- Direct continuation from an earlier source and staged continuation through
one displayed intermediate owner agree after the intermediate occurrence is
reprepared.  This is the induction step that follows a coarse parent root
across one fine child while retaining the parent's direct point query. -/
def directToPreparedContinuationRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left middle target : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (child : Owner
      (polynomial.eval (segment.pointAt middle.parameter)))
    (childRequest : StepRequest)
    (sourceMiddleSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval (segment.pointAt left.parameter) -
          polynomial.eval (segment.pointAt middle.parameter)) <
        source.track.initial.clearance.bound)
    (sourceTargetSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval (segment.pointAt left.parameter) -
          polynomial.eval (segment.pointAt target.parameter)) <
        source.track.initial.clearance.bound)
    (middleEquivalent : NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
        (source.advance
          (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
          sourceMiddleSmall))
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside) child))
    (congruence :
      CCL.Riemann.SquareRootTrackEquivalence.ContinuationCongruenceSmall
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
        (source.advance
          (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
          sourceMiddleSmall)
        (prepared segment middle child childRequest)
        (polynomial.eval (segment.pointAt target.parameter))) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero target.parameter target.inside)
        source sourceTargetSmall)
      (CCL.Riemann.SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero target.parameter target.inside)
        (prepared segment middle child childRequest)
        congruence.secondSmall) := by
  let middleNonzero := segment.pointAt_eval_ne_zero middle.parameter
    middle.inside
  let targetNonzero := segment.pointAt_eval_ne_zero target.parameter
    target.inside
  let middleOwner := source.advance middleNonzero sourceMiddleSmall
  let childPrepared := prepared segment middle child childRequest
  have directToStaged :=
    CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_continued_compose
      middleNonzero targetNonzero source.track sourceMiddleSmall
        sourceTargetSmall congruence.firstSmall
  have childPreparation := sourceRootEquivalent segment middle child
    childRequest
  have middleToPrepared : NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName middleNonzero
        middleOwner)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName middleNonzero
        childPrepared) :=
    CCL.OperationalEquivalence.NamedEquivalent.trans middleEquivalent
      childPreparation
  have stagedToPrepared :=
    CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_continued_of_rootEquivalent
      middleNonzero targetNonzero middleOwner childPrepared middleToPrepared
        congruence
  exact CCL.OperationalEquivalence.NamedEquivalent.trans directToStaged
    stagedToPrepared

/-- Recursive endpoint form of the direct-versus-staged theorem.  The stored
transported endpoint owner is operationally equal to the parent's direct
owner at the same target parameter. -/
def directToAdvanceRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left middle : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (child : Owner
      (polynomial.eval (segment.pointAt middle.parameter)))
    (childRequest : StepRequest)
    (childSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      middle.parameter childRequest.endpoint.parameter <
        (prepared segment middle child childRequest).track.initial.clearance.bound)
    (sourceMiddleSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval (segment.pointAt left.parameter) -
          polynomial.eval (segment.pointAt middle.parameter)) <
        source.track.initial.clearance.bound)
    (sourceTargetSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (polynomial.eval (segment.pointAt left.parameter) -
          polynomial.eval
            (segment.pointAt childRequest.endpoint.parameter)) <
        source.track.initial.clearance.bound)
    (middleEquivalent : NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
        (source.advance
          (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
          sourceMiddleSmall))
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside) child))
    (congruence :
      CCL.Riemann.SquareRootTrackEquivalence.ContinuationCongruenceSmall
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
        (source.advance
          (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
          sourceMiddleSmall)
        (prepared segment middle child childRequest)
        (polynomial.eval
          (segment.pointAt childRequest.endpoint.parameter))) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero childRequest.endpoint.parameter
          childRequest.endpoint.inside)
        (source.advance
          (segment.pointAt_eval_ne_zero childRequest.endpoint.parameter
            childRequest.endpoint.inside)
          sourceTargetSmall))
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero childRequest.endpoint.parameter
          childRequest.endpoint.inside)
        (advance segment within middle child childRequest childSmall)) := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    childRequest.endpoint.parameter childRequest.endpoint.inside
  have directToPrepared := directToPreparedContinuationRootEquivalent segment
    left middle childRequest.endpoint source child childRequest
      sourceMiddleSmall sourceTargetSmall middleEquivalent congruence
  have directToTransported : NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName targetNonzero
        (source.advance targetNonzero sourceTargetSmall))
      (transportedRootName segment within middle child childRequest
        childSmall) := by
    exact CCL.OperationalEquivalence.NamedEquivalent.trans directToPrepared
      (continuedRootNameEquivalentTransportedRootName segment within middle
        child childRequest childSmall)
  have transportedToAdvance := retainedAtReserveRootEquivalent
    (transported segment within middle child childRequest childSmall)
      (preparedClearanceLower segment middle childRequest)
  simpa only [advance, transportedRootName,
    CCL.Riemann.SquareRootTrackEquivalence.ownerRootName] using
      CCL.OperationalEquivalence.NamedEquivalent.trans directToTransported
        transportedToAdvance

/-- Uniform preparation followed by a mesh-safe congruent Rouché move
preserves operational root equivalence.  This is the edge-level induction
step used to compare differently subdivided dyadic continuations. -/
def preparedContinuationRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (sourceEquivalent : NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second))
    (small : VariationCongruenceSmall segment left request.endpoint
      (prepared segment left first request)
      (prepared segment left second request)) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        (prepared segment left first request)
        (small.toContinuationCongruenceSmall within).firstSmall)
      (CCL.Riemann.SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        (prepared segment left second request)
        (small.toContinuationCongruenceSmall within).secondSmall) := by
  exact preparedContinuationAtRootEquivalent segment within left first second
    request request request.endpoint sourceEquivalent small

/-- Endpoint-name form of `preparedContinuationRootEquivalent`.  It exposes
the actual transported owners used by accepted prepared edges, so recursive
subdivision comparisons need no unfolding of the Rouché implementation. -/
def transportedRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (sourceEquivalent : NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second))
    (small : VariationCongruenceSmall segment left request.endpoint
      (prepared segment left first request)
      (prepared segment left second request)) :
    NamedEquivalent
      (transportedRootName segment within left first request small.firstSmall)
      (transportedRootName segment within left second request
        small.secondSmall) := by
  have firstGenericToTransported :=
    continuedRootNameEquivalentTransportedRootName segment within left first
      request small.firstSmall
  have genericEquivalent :=
    preparedContinuationRootEquivalent segment within left first second
      request sourceEquivalent small
  have secondGenericToTransported :=
    continuedRootNameEquivalentTransportedRootName segment within left second
      request small.secondSmall
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    firstGenericToTransported.symm
    (CCL.OperationalEquivalence.NamedEquivalent.trans genericEquivalent
      secondGenericToTransported)

/-- Congruent accepted edges retain operationally equivalent transported
endpoint owners. -/
def advanceRootEquivalent_of_rootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (sourceEquivalent : NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second))
    (small : VariationCongruenceSmall segment left request.endpoint
      (prepared segment left first request)
      (prepared segment left second request)) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        (advance segment within left first request small.firstSmall))
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        (advance segment within left second request small.secondSmall)) := by
  let firstTransported := transported segment within left first request
    small.firstSmall
  let secondTransported := transported segment within left second request
    small.secondSmall
  have transportedEquivalent := transportedRootEquivalent segment within left
    first second request sourceEquivalent small
  have firstReset := retainedAtReserveRootEquivalent firstTransported
    (preparedClearanceLower segment left request)
  have secondReset := retainedAtReserveRootEquivalent secondTransported
    (preparedClearanceLower segment left request)
  have resetEquivalent :=
    CCL.OperationalEquivalence.NamedEquivalent.trans firstReset.symm
      (CCL.OperationalEquivalence.NamedEquivalent.trans transportedEquivalent
        secondReset)
  simpa only [advance, firstTransported, secondTransported, transportedRootName,
    CCL.Riemann.SquareRootTrackEquivalence.ownerRootName] using resetEquivalent

/-! ## Sheet-independent finite mesh checks -/

/-- The prepared clearance of one explicitly indexed canonical square-root
owner at the current rational base point. -/
def canonicalPreparedClearance {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) (index : Fin 2) :
    Coordinate :=
  (prepared
    segment current
    (CCL.Riemann.SquareRootReconditioning.canonicalOwner
      (segment.pointAt_eval_ne_zero current.parameter current.inside) index)
    request).track.initial.clearance.bound

/-- A positive rational clearance valid for either canonical sheet owner.
Only two finite values are inspected. -/
def canonicalPreparedClearanceFloor {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) : Coordinate :=
  min
    (canonicalPreparedClearance segment current request
      (⟨0, by decide⟩ : Fin 2))
    (canonicalPreparedClearance segment current request
      (⟨1, by decide⟩ : Fin 2))

theorem canonicalPreparedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) :
    0 < canonicalPreparedClearanceFloor segment current request := by
  apply lt_min
  · exact (prepared
      segment current
      (CCL.Riemann.SquareRootReconditioning.canonicalOwner
        (segment.pointAt_eval_ne_zero current.parameter current.inside)
          (⟨0, by decide⟩ : Fin 2)) request).track.initial.clearance.positive
  · exact (prepared
      segment current
      (CCL.Riemann.SquareRootReconditioning.canonicalOwner
        (segment.pointAt_eval_ne_zero current.parameter current.inside)
          (⟨1, by decide⟩ : Fin 2)) request).track.initial.clearance.positive

theorem canonicalPreparedClearanceFloor_le
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) (index : Fin 2) :
    canonicalPreparedClearanceFloor segment current request <=
      canonicalPreparedClearance segment current request index := by
  cases index using Fin.cases with
  | zero => exact min_le_left _ _
  | succ index =>
      cases index using Fin.cases with
      | zero => exact min_le_right _ _
      | succ impossible => exact Fin.elim0 impossible

/-- The finite two-owner floor bounds the prepared clearance after every
reconditioning, without exposing which sheet the assignment selected. -/
theorem canonicalPreparedClearanceFloor_le_freshOwner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    canonicalPreparedClearanceFloor segment current request <=
      (prepared
        segment current
        (CCL.Riemann.SquareRootReconditioning.freshOwner
          (segment.pointAt_eval_ne_zero current.parameter current.inside) owner)
        request).track.initial.clearance.bound := by
  rw [CCL.Riemann.SquareRootReconditioning.freshOwner_eq_canonicalOwner]
  exact canonicalPreparedClearanceFloor_le segment current request _

/-- The explicit predicted preparation clearance for one canonical sheet at
the current rational base point. -/
def canonicalPredictedClearance {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) (_index : Fin 2) :
    Coordinate :=
  preparedClearanceLower segment current request

/-- A finite predicted clearance valid for either canonical sheet. -/
def canonicalPredictedClearanceFloor {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) : Coordinate :=
  min
    (canonicalPredictedClearance segment current request
      (⟨0, by decide⟩ : Fin 2))
    (canonicalPredictedClearance segment current request
      (⟨1, by decide⟩ : Fin 2))

theorem canonicalPredictedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) :
    0 < canonicalPredictedClearanceFloor segment current request := by
  apply lt_min <;>
    exact preparedClearanceLower_positive segment current request

theorem canonicalPredictedClearanceFloor_le_actual
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) :
    canonicalPredictedClearanceFloor segment current request ≤
      canonicalPreparedClearanceFloor segment current request := by
  unfold canonicalPredictedClearanceFloor canonicalPreparedClearanceFloor
    canonicalPredictedClearance canonicalPreparedClearance
  exact min_le_min
    (preparedClearanceLower_le segment current _ request)
    (preparedClearanceLower_le segment current _ request)

/-- The predicted two-sheet floor bounds the prepared clearance of every
inherited owner, not merely one of the globally reconditioned owners. -/
theorem canonicalPredictedClearanceFloor_le_prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    canonicalPredictedClearanceFloor segment current request ≤
      (prepared segment current owner request).track.initial.clearance.bound :=
  (min_le_left _ _).trans
    (preparedClearanceLower_le segment current owner request)

/-- Owner-independent safety of every transported tail move.  Each inequality
uses the uniform predicted preparation clearance, so it is unaffected by the
particular inherited presentation of the same sheet occurrence. -/
def FreshMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    Endpoint -> List StepRequest -> Prop
  | _current, [] => True
  | current, request :: remaining =>
      current.parameter <= request.endpoint.parameter ∧
        CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          canonicalPredictedClearanceFloor segment current request ∧
        FreshMeshSafe segment request.endpoint remaining

/-- Safety of a complete displayed mesh.  Only its first move mentions the
supplied owner; every later move uses the owner-independent predicted
preparation floor. -/
def MeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    List StepRequest -> Prop
  | [] => True
  | request :: remaining =>
      current.parameter <= request.endpoint.parameter ∧
        CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          (prepared segment current owner request).track.initial.clearance.bound ∧
        FreshMeshSafe segment request.endpoint remaining

/-- Every tail mesh-safety condition is decidable by a finite scan of
rational inequalities. -/
instance freshMeshSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint) (requests : List StepRequest) :
    Decidable (FreshMeshSafe segment current requests) := by
  induction requests generalizing current with
  | nil => exact isTrue trivial
  | cons request remaining inductionHypothesis =>
      simp only [FreshMeshSafe]
      letI := inductionHypothesis request.endpoint
      infer_instance

/-- Complete mesh safety is likewise one executable finite decision. -/
instance meshSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest) :
    Decidable (MeshSafe segment current owner requests) := by
  cases requests with
  | nil => exact isTrue trivial
  | cons request remaining =>
      simp only [MeshSafe]
      infer_instance

/-- A finite dependent walk carrying a diameter request and its already
evaluated prepared source at every edge. -/
inductive Subdivision {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (left : Endpoint) ->
      Owner (polynomial.eval (segment.pointAt left.parameter)) -> Type
  | stop (left : Endpoint)
      (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) :
      Subdivision segment within left owner
  | next (left : Endpoint)
      (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
      (request : StepRequest)
      (cached : CachedSource segment left owner request)
      (ordered : left.parameter <= request.endpoint.parameter)
      (small : CCL.Riemann.ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
      (remaining : Subdivision segment within request.endpoint
        (advance segment within left owner request small)) :
      Subdivision segment within left owner

namespace Subdivision

/-- Reindex a prepared tail across equality of its endpoint owner.  The
equality is proof-only, so compiled execution retains the already evaluated
subdivision without rebuilding either owner. -/
def castOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    Subdivision segment within left second := by
  cases equal
  exact subdivision

/-- Add an accepted edge whose recursive tail was computed from the cached
prepared source.  Only the erased owner-equality cast connects it to the
canonical `advance` specification stored by `Subdivision.next`. -/
def nextCached {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    Subdivision segment within left owner :=
  .next left owner request cached ordered canonicalSmall
    (remaining.castOwner
      (advanceCached_eq_advance segment within left owner request cached
        cachedSmall canonicalSmall))

def endpoint {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))} :
    Subdivision segment within left owner -> Endpoint
  | .stop endpoint _ => endpoint
  | .next _ _ _ _ _ _ remaining => remaining.endpoint

def terminalOwner {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))} :
    (subdivision : Subdivision segment within left owner) ->
      Owner (polynomial.eval
        (segment.pointAt subdivision.endpoint.parameter))
  | .stop _ owner => owner
  | .next _ _ _ _ _ _ remaining => remaining.terminalOwner

def stepCount {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))} :
    Subdivision segment within left owner -> Nat
  | .stop _ _ => 0
  | .next _ _ _ _ _ _ remaining => remaining.stepCount + 1

/-- Direct source-to-endpoint smallness, kept as one compact proof record for
dependent coarse/fine recursion. -/
structure DirectMoveSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (current : Endpoint) : Prop where
  proof : RFAP.ConstructiveGaussian.Gaussian.normSq
    (polynomial.eval (segment.pointAt origin.parameter) -
      polynomial.eval (segment.pointAt current.parameter)) <
    source.track.initial.clearance.bound

/-- Direct owner obtained from one fixed parent source at a displayed later
endpoint. -/
def directOwnerAt {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (current : Endpoint)
    (small : DirectMoveSmall segment origin source current) :
    Owner (polynomial.eval (segment.pointAt current.parameter)) :=
  source.advance
    (segment.pointAt_eval_ne_zero current.parameter current.inside) small.proof

/-- Compact operational relation between two owner presentations at the same
displayed base endpoint. -/
structure RootEquivalentAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt current.parameter))) where
  firstName : Named
  secondName : Named
  equivalent : NamedEquivalent firstName secondName
  first_eq : firstName =
    CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero current.parameter current.inside) first
  second_eq : secondName =
    CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero current.parameter current.inside) second

namespace RootEquivalentAt

/-- Recover the endpoint-indexed operational relation after elaborating the
two productive names independently. -/
def toNamedEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {current : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt current.parameter))}
    (relation : RootEquivalentAt segment current first second) :
    NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero current.parameter current.inside) first)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero current.parameter current.inside)
        second) := by
  rw [← relation.first_eq, ← relation.second_eq]
  exact relation.equivalent

end RootEquivalentAt

/-- The canonical zero-displacement direct-move certificate. -/
theorem sameDirectMoveSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter))) :
    DirectMoveSmall segment origin source origin :=
  ⟨samePointSmall source⟩

/-- At the parent's starting point, its zero move is operationally equivalent
to any supplied presentation of the same source occurrence. -/
def initialDirectRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    (origin : Endpoint)
    (source owner : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (equivalent : RootEquivalentAt segment origin source owner) :
    RootEquivalentAt segment origin
      (directOwnerAt origin source origin (sameDirectMoveSmall origin source))
      owner :=
  { firstName := CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero origin.parameter origin.inside)
      (directOwnerAt origin source origin (sameDirectMoveSmall origin source))
    secondName := CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero origin.parameter origin.inside) owner
    equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_advance_same
        (segment.pointAt_eval_ne_zero origin.parameter origin.inside) source
          (sameDirectMoveSmall origin source).proof).symm
      equivalent.toNamedEquivalent
    first_eq := rfl
    second_eq := rfl }

/-- The seven continuation-congruence inequalities for one recursive fine
step, hidden behind the direct/current owner indices. -/
structure DirectStepSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (current : Endpoint)
    (sourceCurrentSmall : DirectMoveSmall segment origin source current)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) : Prop where
  congruence :
    CCL.Riemann.SquareRootTrackEquivalence.ContinuationCongruenceSmall
      (segment.pointAt_eval_ne_zero current.parameter current.inside)
      (directOwnerAt origin source current sourceCurrentSmall)
      (prepared segment current owner request)
      (polynomial.eval (segment.pointAt request.endpoint.parameter))

instance directStepSmallDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (current : Endpoint)
    (sourceCurrentSmall : DirectMoveSmall segment origin source current)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    Decidable (DirectStepSmall segment origin source current
      sourceCurrentSmall owner request) := by
  by_cases congruence :
      CCL.Riemann.SquareRootTrackEquivalence.ContinuationCongruenceSmall
        (segment.pointAt_eval_ne_zero current.parameter current.inside)
        (directOwnerAt origin source current sourceCurrentSmall)
        (prepared segment current owner request)
        (polynomial.eval (segment.pointAt request.endpoint.parameter))
  · exact isTrue ⟨congruence⟩
  · exact isFalse (fun small => congruence small.congruence)

/-- Compute the next direct/current root relation from one fine accepted
step. -/
def directNextRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter)))
    (current : Endpoint)
    (sourceCurrentSmall : DirectMoveSmall segment origin source current)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (currentEquivalent : RootEquivalentAt segment current
      (directOwnerAt origin source current sourceCurrentSmall) owner)
    (request : StepRequest)
    (childSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        (prepared segment current owner request).track.initial.clearance.bound)
    (sourceNextSmall : DirectMoveSmall segment origin source request.endpoint)
    (stepSmall : DirectStepSmall segment origin source current
      sourceCurrentSmall owner request) :
    RootEquivalentAt segment request.endpoint
      (directOwnerAt origin source request.endpoint sourceNextSmall)
      (advance segment within current owner request childSmall) :=
  { firstName := CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      (directOwnerAt origin source request.endpoint sourceNextSmall)
    secondName := CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      (advance segment within current owner request childSmall)
    equivalent := directToAdvanceRootEquivalent segment within origin current
      source owner request childSmall sourceCurrentSmall.proof
        sourceNextSmall.proof currentEquivalent.toNamedEquivalent
          stepSmall.congruence
    first_eq := rfl
    second_eq := rfl }

/-- A fine prepared subdivision followed inside one fixed parent occurrence.
The only recursive inputs are compact rational move and clearance records;
the next root relation is computed rather than supplied. -/
inductive DirectlyCoherent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (origin : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt origin.parameter))) :
    {current : Endpoint} ->
      (sourceCurrentSmall : DirectMoveSmall segment origin source current) ->
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter))) ->
      RootEquivalentAt segment current
        (directOwnerAt origin source current sourceCurrentSmall) owner ->
      Subdivision segment within current owner -> Type 2
  | stop
      (current : Endpoint)
      (sourceCurrentSmall : DirectMoveSmall segment origin source current)
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter)))
      (currentEquivalent : RootEquivalentAt segment current
        (directOwnerAt origin source current sourceCurrentSmall) owner) :
      DirectlyCoherent segment within origin source sourceCurrentSmall owner
        currentEquivalent (.stop current owner)
  | next
      (current : Endpoint)
      (sourceCurrentSmall : DirectMoveSmall segment origin source current)
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter)))
      (currentEquivalent : RootEquivalentAt segment current
        (directOwnerAt origin source current sourceCurrentSmall) owner)
      (request : StepRequest)
      (cached : CachedSource segment current owner request)
      (ordered : current.parameter <= request.endpoint.parameter)
      (childSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
        current.parameter request.endpoint.parameter <
          (prepared segment current owner request).track.initial.clearance.bound)
      (remaining : Subdivision segment within request.endpoint
        (advance segment within current owner request childSmall))
      (sourceNextSmall : DirectMoveSmall segment origin source request.endpoint)
      (stepSmall : DirectStepSmall segment origin source current
        sourceCurrentSmall owner request)
      (tail : DirectlyCoherent segment within origin source sourceNextSmall
        (advance segment within current owner request childSmall)
        (directNextRootEquivalent segment within origin source current
          sourceCurrentSmall owner currentEquivalent request childSmall
            sourceNextSmall stepSmall)
        remaining) :
      DirectlyCoherent segment within origin source sourceCurrentSmall owner
        currentEquivalent
          (.next current owner request cached ordered childSmall remaining)

/-- Retain the exact left and right parameter endpoints of every accepted
prepared step. -/
def parameterEdges {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))} :
    Subdivision segment within left owner ->
      List CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge
  | .stop _ _ => []
  | .next left _owner request _cached _ordered _small remaining =>
      { left := left, right := request.endpoint } :: remaining.parameterEdges

/-- Retain the exact endpoint-and-diameter request accepted at every prepared
step.  Unlike `parameterEdges`, this cache also records the requested root
diameter needed by owner-independent integration bounds. -/
def requests {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))} :
    Subdivision segment within left owner -> List StepRequest
  | .stop _ _ => []
  | .next _left _owner request _cached _ordered _small remaining =>
      request :: remaining.requests

/-- The retained parameter-edge cache has one entry for every accepted
prepared step. -/
@[simp] theorem parameterEdges_length
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.parameterEdges.length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next _left _owner _request _cached _ordered _small remaining
      inductionHypothesis =>
      simp only [parameterEdges, List.length_cons, stepCount,
        inductionHypothesis]

@[simp] theorem requests_length
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.requests.length = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next _left _owner _request _cached _ordered _small remaining
      inductionHypothesis =>
      simp only [requests, List.length_cons, stepCount, inductionHypothesis]

@[simp] theorem castOwner_endpoint
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).endpoint = subdivision.endpoint := by
  cases equal
  rfl

@[simp] theorem nextCached_endpoint
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).endpoint = remaining.endpoint := by
  simp only [nextCached, endpoint, castOwner_endpoint]

@[simp] theorem castOwner_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).stepCount = subdivision.stepCount := by
  cases equal
  rfl

@[simp] theorem castOwner_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).parameterEdges =
      subdivision.parameterEdges := by
  cases equal
  rfl

@[simp] theorem castOwner_requests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).requests = subdivision.requests := by
  cases equal
  rfl

@[simp] theorem nextCached_stepCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).stepCount = remaining.stepCount + 1 := by
  simp only [nextCached, stepCount, castOwner_stepCount]

@[simp] theorem nextCached_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).parameterEdges =
        { left := left, right := request.endpoint } ::
          remaining.parameterEdges := by
  simp only [nextCached, parameterEdges, castOwner_parameterEdges]

@[simp] theorem nextCached_requests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).requests = request :: remaining.requests := by
  simp only [nextCached, requests, castOwner_requests]

/-- Total checker for a displayed sequence of endpoint/diameter requests. -/
def trySteps {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter))) :
    (requests : List StepRequest) ->
      Option (Subdivision segment within left owner)
  | [] => some (.stop left owner)
  | request :: remaining =>
      let cached := CachedSource.canonical segment left owner request
      if ordered : left.parameter <= request.endpoint.parameter then
        if cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
            left.parameter request.endpoint.parameter <
              cached.preparedOwner.track.initial.clearance.bound then
          let small : CCL.Riemann.ClearSheetContinuation.variationBound segment
              left.parameter request.endpoint.parameter <
                (prepared segment left owner request).track.initial.clearance.bound := by
            rw [cached.preparedOwner_eq] at cachedSmall
            exact cachedSmall
          let nextOwner := advanceCached segment within left owner request
            cached cachedSmall
          match trySteps segment within request.endpoint
              nextOwner remaining with
          | none => none
          | some tail =>
              some (nextCached segment within left owner request cached
                ordered cachedSmall small tail)
        else none
      else none

/-- The exact finite comparisons followed by `trySteps`, recorded as an
erased proof certificate.  Unlike `MeshSafe`, every recursive edge may use
the actually transported owner retained from its predecessor. -/
def ExecutedMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (current : Endpoint) ->
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter))) ->
          List StepRequest -> Prop
  | _current, _owner, [] => True
  | current, owner, request :: remaining =>
      let cached := CachedSource.canonical segment current owner request
      current.parameter <= request.endpoint.parameter ∧
        if small : CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
              cached.preparedOwner.track.initial.clearance.bound then
          ExecutedMeshSafe segment within request.endpoint
            (advanceCached segment within current owner request cached small)
            remaining
        else False

/-- Exact executed-mesh safety remains decidable by a finite scan of the
same rational comparisons used by `trySteps`. -/
instance executedMeshSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (current : Endpoint) ->
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter))) ->
          (requests : List StepRequest) ->
            Decidable (ExecutedMeshSafe segment within current owner requests)
  | _current, _owner, [] => isTrue trivial
  | current, owner, request :: remaining => by
      let cached := CachedSource.canonical segment current owner request
      if ordered : current.parameter <= request.endpoint.parameter then
        if small : CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
              cached.preparedOwner.track.initial.clearance.bound then
          letI := executedMeshSafeDecidable segment within request.endpoint
            (advanceCached segment within current owner request cached small)
              remaining
          exact decidable_of_iff
            (ExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached small)
                remaining)
            (by
              constructor
              · intro tail
                change current.parameter <= request.endpoint.parameter ∧
                  (if witness :
                      CCL.Riemann.ClearSheetContinuation.variationBound segment
                          current.parameter request.endpoint.parameter <
                        cached.preparedOwner.track.initial.clearance.bound then
                    ExecutedMeshSafe segment within request.endpoint
                      (advanceCached segment within current owner request cached
                        witness) remaining
                  else False)
                exact ⟨ordered, by simpa only [dif_pos small] using tail⟩
              · intro safe
                have right := safe.2
                change (if witness :
                    CCL.Riemann.ClearSheetContinuation.variationBound segment
                        current.parameter request.endpoint.parameter <
                      cached.preparedOwner.track.initial.clearance.bound then
                  ExecutedMeshSafe segment within request.endpoint
                    (advanceCached segment within current owner request cached
                      witness) remaining
                else False) at right
                simpa only [dif_pos small] using right)
        else
          exact isFalse (fun safe => by
            have right := safe.2
            change (if witness :
                CCL.Riemann.ClearSheetContinuation.variationBound segment
                    current.parameter request.endpoint.parameter <
                  cached.preparedOwner.track.initial.clearance.bound then
              ExecutedMeshSafe segment within request.endpoint
                (advanceCached segment within current owner request cached
                  witness) remaining
            else False) at right
            rw [dif_neg small] at right
            exact right)
      else
        exact isFalse (fun safe => ordered safe.1)

/-- Construct the dependent continuation walk directly from an exact
executed-mesh certificate.  The comparison proofs are erased at runtime. -/
def ofExecutedMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (current : Endpoint) ->
      (owner : Owner
        (polynomial.eval (segment.pointAt current.parameter))) ->
          (requests : List StepRequest) ->
            ExecutedMeshSafe segment within current owner requests ->
              Subdivision segment within current owner
  | current, owner, [], _safe => .stop current owner
  | current, owner, request :: remaining, safe => by
      let cached := CachedSource.canonical segment current owner request
      if small : CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
            cached.preparedOwner.track.initial.clearance.bound then
        have tail : ExecutedMeshSafe segment within request.endpoint
            (advanceCached segment within current owner request cached small)
              remaining := by
          have right := safe.2
          change (if witness :
              CCL.Riemann.ClearSheetContinuation.variationBound segment
                  current.parameter request.endpoint.parameter <
                cached.preparedOwner.track.initial.clearance.bound then
            ExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached
                witness) remaining
          else False) at right
          simpa only [dif_pos small] using right
        have canonicalSmall :
            CCL.Riemann.ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
              (prepared segment current owner request).track.initial.clearance.bound := by
          rw [cached.preparedOwner_eq] at small
          exact small
        exact nextCached segment within current owner request cached safe.1
          small canonicalSmall
            (ofExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached small)
                remaining tail)
      else
        have impossible : False := by
          have right := safe.2
          change (if witness :
              CCL.Riemann.ClearSheetContinuation.variationBound segment
                  current.parameter request.endpoint.parameter <
                cached.preparedOwner.track.initial.clearance.bound then
            ExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached
                witness) remaining
          else False) at right
          simp only [dif_neg small] at right
        exact impossible.elim

/-- The ordinary executable checker returns exactly the subdivision rebuilt
from its erased successful-comparison certificate. -/
theorem trySteps_eq_some_ofExecutedMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    {current : Endpoint}
    {owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))}
    (requests : List StepRequest)
    (safe : ExecutedMeshSafe segment within current owner requests) :
    trySteps segment within current owner requests =
      some (ofExecutedMeshSafe segment within current owner requests safe) := by
  induction requests generalizing current owner with
  | nil => rfl
  | cons request remaining inductionHypothesis =>
      let cached := CachedSource.canonical segment current owner request
      if small : CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
            cached.preparedOwner.track.initial.clearance.bound then
        have tail : ExecutedMeshSafe segment within request.endpoint
            (advanceCached segment within current owner request cached small)
              remaining := by
          have right := safe.2
          change (if witness :
              CCL.Riemann.ClearSheetContinuation.variationBound segment
                  current.parameter request.endpoint.parameter <
                cached.preparedOwner.track.initial.clearance.bound then
            ExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached
                witness) remaining
          else False) at right
          simpa only [dif_pos small] using right
        rw [trySteps]
        dsimp only
        rw [dif_pos safe.1, dif_pos small, inductionHypothesis tail]
        let canonicalSafe : ExecutedMeshSafe segment within current owner
            (request :: remaining) := by
          change current.parameter <= request.endpoint.parameter ∧
            (if witness :
                CCL.Riemann.ClearSheetContinuation.variationBound segment
                    current.parameter request.endpoint.parameter <
                  cached.preparedOwner.track.initial.clearance.bound then
              ExecutedMeshSafe segment within request.endpoint
                (advanceCached segment within current owner request cached
                  witness) remaining
            else False)
          exact ⟨safe.1, by simpa only [dif_pos small] using tail⟩
        have safeEqual : safe = canonicalSafe := Subsingleton.elim _ _
        have outputEqual :
            ofExecutedMeshSafe segment within current owner
                (request :: remaining) safe =
              ofExecutedMeshSafe segment within current owner
                (request :: remaining) canonicalSafe :=
          congrArg
            (fun proof : ExecutedMeshSafe segment within current owner
                (request :: remaining) =>
              ofExecutedMeshSafe segment within current owner
                (request :: remaining) proof)
            safeEqual
        calc
          _ = some (ofExecutedMeshSafe segment within current owner
              (request :: remaining) canonicalSafe) := by
                dsimp only [canonicalSafe, ofExecutedMeshSafe]
                split
                · rfl
                · contradiction
          _ = some (ofExecutedMeshSafe segment within current owner
              (request :: remaining) safe) :=
                congrArg some outputEqual.symm
      else
        have impossible : False := by
          have right := safe.2
          change (if witness :
              CCL.Riemann.ClearSheetContinuation.variationBound segment
                  current.parameter request.endpoint.parameter <
                cached.preparedOwner.track.initial.clearance.bound then
            ExecutedMeshSafe segment within request.endpoint
              (advanceCached segment within current owner request cached
                witness) remaining
          else False) at right
          simp only [dif_neg small] at right
        exact impossible.elim

/-- Construct the dependent continuation walk from owner-independent tail
safety.  The transported endpoint owner is threaded directly, while the
uniform predicted floor supplies every recursive smallness proof. -/
def ofFreshMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (prior : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    (requests : List StepRequest) ->
      FreshMeshSafe segment current requests ->
        Subdivision segment within current prior
  | [], _safe => .stop current prior
  | request :: remaining, safe =>
      let small : CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
          (prepared segment current prior request).track.initial.clearance.bound :=
        safe.2.1.trans_le
          (canonicalPredictedClearanceFloor_le_prepared segment current prior
            request)
      let cached := CachedSource.canonical segment current prior request
      let cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound
          segment current.parameter request.endpoint.parameter <
            cached.preparedOwner.track.initial.clearance.bound := small
      let nextOwner := advanceCached segment within current prior request
        cached cachedSmall
      nextCached segment within current prior request cached safe.1 cachedSmall
        small (ofFreshMeshSafe segment within request.endpoint nextOwner
          remaining safe.2.2)

/-- Construct the complete dependent continuation walk from one finite mesh
safety proof.  The first move uses the supplied owner and the remaining moves
are discharged by the two-owner canonical clearance floor. -/
def ofMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter))) :
    (requests : List StepRequest) -> MeshSafe segment current owner requests ->
      Subdivision segment within current owner
  | [], _safe => .stop current owner
  | request :: remaining, safe =>
      let cached := CachedSource.canonical segment current owner request
      let cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound
          segment current.parameter request.endpoint.parameter <
            cached.preparedOwner.track.initial.clearance.bound := safe.2.1
      let nextOwner := advanceCached segment within current owner request
        cached cachedSmall
      nextCached segment within current owner request cached safe.1 cachedSmall
        safe.2.1 (ofFreshMeshSafe segment within request.endpoint nextOwner
          remaining safe.2.2)

/-- The executable checker accepts the subdivision constructed from every
sheet-independent safe tail. -/
theorem trySteps_eq_some_ofFreshMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (prior : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest)
    (safe : FreshMeshSafe segment current requests) :
    trySteps segment within current prior requests =
      some (ofFreshMeshSafe segment within current prior requests safe) := by
  induction requests generalizing current prior with
  | nil => rfl
  | cons request remaining inductionHypothesis =>
      let small : CCL.Riemann.ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
          (prepared segment current prior request).track.initial.clearance.bound :=
        safe.2.1.trans_le
          (canonicalPredictedClearanceFloor_le_prepared segment current prior
            request)
      have cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound
          segment current.parameter request.endpoint.parameter <
            ((CachedSource.canonical segment current prior request).preparedOwner).track.initial.clearance.bound :=
        small
      simp only [trySteps, dif_pos safe.1, dif_pos cachedSmall]
      let nextOwner := advanceCached segment within current prior request
        (CachedSource.canonical segment current prior request) cachedSmall
      have tailSuccess :
          trySteps segment within request.endpoint
              nextOwner remaining =
            some (ofFreshMeshSafe segment within request.endpoint
              nextOwner remaining safe.2.2) := by
        exact inductionHypothesis request.endpoint
          nextOwner safe.2.2
      rw [tailSuccess]
      rfl

/-- The executable checker accepts the subdivision constructed from a finite
mesh safety proof. -/
theorem trySteps_eq_some_ofMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner
      (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest)
    (safe : MeshSafe segment current owner requests) :
    trySteps segment within current owner requests =
      some (ofMeshSafe segment within current owner requests safe) := by
  cases requests with
  | nil => rfl
  | cons request remaining =>
      have cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound
          segment current.parameter request.endpoint.parameter <
            ((CachedSource.canonical segment current owner request).preparedOwner).track.initial.clearance.bound :=
        safe.2.1
      simp only [trySteps, dif_pos safe.1, dif_pos cachedSmall]
      let nextOwner := advanceCached segment within current owner request
        (CachedSource.canonical segment current owner request) cachedSmall
      have tailSuccess :
          trySteps segment within request.endpoint
              nextOwner remaining =
            some (ofFreshMeshSafe segment within request.endpoint
              nextOwner remaining safe.2.2) := by
        exact trySteps_eq_some_ofFreshMeshSafe segment within request.endpoint
          nextOwner remaining safe.2.2
      rw [tailSuccess]
      rfl

theorem trySteps_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests =
      some subdivision) :
    subdivision.stepCount = requests.length := by
  induction requests generalizing left owner subdivision with
  | nil =>
      simp only [trySteps] at success
      cases success
      rfl
  | cons request remaining inductionHypothesis =>
      simp only [trySteps] at success
      split at success
      next ordered =>
        split at success
        next small =>
          split at success
          next failure => contradiction
          next tail recursiveSuccess =>
            cases success
            simp only [nextCached_stepCount, List.length_cons]
            exact congrArg Nat.succ
              (inductionHypothesis request.endpoint
                (advanceCached segment within left owner request
                  (CachedSource.canonical segment left owner request) small)
                (subdivision := tail) recursiveSuccess)
        next notSmall => contradiction
      next notOrdered => contradiction

def finalTarget (current : Endpoint) : List StepRequest -> Endpoint
  | [] => current
  | request :: remaining => finalTarget request.endpoint remaining

def requestEndpoints : List StepRequest -> List Endpoint
  | [] => []
  | request :: remaining => request.endpoint :: requestEndpoints remaining

/-- A successful prepared walk retains precisely the consecutive edges of
its displayed request endpoints. -/
theorem trySteps_parameterEdges {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests =
      some subdivision) :
    subdivision.parameterEdges =
      CCL.Riemann.ClearSheetContinuation.Subdivision.parameterEdgesFrom left
        (requestEndpoints requests) := by
  induction requests generalizing left owner subdivision with
  | nil =>
      simp only [trySteps] at success
      cases success
      rfl
  | cons request remaining inductionHypothesis =>
      simp only [trySteps] at success
      split at success
      next ordered =>
        split at success
        next small =>
          split at success
          next failure => contradiction
          next tail recursiveSuccess =>
            cases success
            simp only [nextCached_parameterEdges, requestEndpoints,
              CCL.Riemann.ClearSheetContinuation.Subdivision.parameterEdgesFrom]
            exact congrArg
              (List.cons
                (CCL.Riemann.ClearSheetContinuation.Subdivision.ParameterEdge.mk
                  left request.endpoint))
              (inductionHypothesis request.endpoint
                (advanceCached segment within left owner request
                  (CachedSource.canonical segment left owner request) small)
                (subdivision := tail) recursiveSuccess)
        next notSmall => contradiction
      next notOrdered => contradiction

/-- A successful prepared walk retains exactly the displayed request list,
including every endpoint and requested root diameter. -/
theorem trySteps_requests {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests = some subdivision) :
    subdivision.requests = requests := by
  induction requests generalizing left owner subdivision with
  | nil =>
      simp only [trySteps] at success
      cases success
      rfl
  | cons request remaining inductionHypothesis =>
      simp only [trySteps] at success
      split at success
      next ordered =>
        split at success
        next small =>
          split at success
          next failure => contradiction
          next tail recursiveSuccess =>
            cases success
            simp only [nextCached_requests]
            exact congrArg (List.cons request)
              (inductionHypothesis request.endpoint
                (advanceCached segment within left owner request
                  (CachedSource.canonical segment left owner request) small)
                (subdivision := tail) recursiveSuccess)
        next notSmall => contradiction
      next notOrdered => contradiction

/-- Positive minimum of the owner-independent predicted clearances appearing
along a displayed transported tail.  The empty tail uses the harmless
positive unit. -/
def FreshMeshClearanceFloor {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    Endpoint -> List StepRequest -> Coordinate
  | _current, [] => 1
  | current, request :: remaining =>
      min (canonicalPredictedClearanceFloor segment current request)
        (FreshMeshClearanceFloor segment request.endpoint remaining)

/-- Positive minimum of every clearance used by one complete prepared mesh,
including the supplied owner on the first edge and the owner-independent
predicted floors on its tail. -/
def MeshClearanceFloor {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    List StepRequest -> Coordinate
  | [] => 1
  | request :: remaining =>
      min (prepared segment current owner request).track.initial.clearance.bound
        (FreshMeshClearanceFloor segment request.endpoint remaining)

/-- Minimum of the a-priori Newton-clearance predictions on every canonical
tail edge of a displayed mesh. -/
def FreshMeshPredictedClearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    Endpoint -> List StepRequest -> Coordinate
  | _current, [] => 1
  | current, request :: remaining =>
      min (canonicalPredictedClearanceFloor segment current request)
        (FreshMeshPredictedClearanceFloor segment request.endpoint remaining)

/-- A-priori clearance minimum for the complete mesh, including its supplied
first owner.  Every term is computed from data available before its separated
Newton extraction is run. -/
def MeshPredictedClearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (_owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    List StepRequest -> Coordinate
  | [] => 1
  | request :: remaining =>
      min (preparedClearanceLower segment current request)
        (FreshMeshPredictedClearanceFloor segment request.endpoint remaining)

theorem freshMeshPredictedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    forall (current : Endpoint) (requests : List StepRequest),
      0 < FreshMeshPredictedClearanceFloor segment current requests
  | _current, [] => by
      change (0 : Coordinate) < 1
      decide
  | current, request :: remaining => by
      apply lt_min
      · exact canonicalPredictedClearanceFloor_positive segment current request
      · exact freshMeshPredictedClearanceFloor_positive segment
          request.endpoint remaining

theorem meshPredictedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    forall requests : List StepRequest,
      0 < MeshPredictedClearanceFloor segment current owner requests
  | [] => by
      change (0 : Coordinate) < 1
      decide
  | request :: remaining => by
      apply lt_min
      · exact preparedClearanceLower_positive segment current request
      · exact freshMeshPredictedClearanceFloor_positive segment
          request.endpoint remaining

theorem freshMeshPredictedClearanceFloor_le_actual
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    forall (current : Endpoint) (requests : List StepRequest),
      FreshMeshPredictedClearanceFloor segment current requests ≤
        FreshMeshClearanceFloor segment current requests
  | _current, [] => le_rfl
  | _current, request :: remaining =>
      min_le_min
        le_rfl
        (freshMeshPredictedClearanceFloor_le_actual segment request.endpoint
          remaining)

theorem meshPredictedClearanceFloor_le_actual
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    forall requests : List StepRequest,
      MeshPredictedClearanceFloor segment current owner requests ≤
        MeshClearanceFloor segment current owner requests
  | [] => le_rfl
  | request :: remaining =>
      min_le_min (preparedClearanceLower_le segment current owner request)
        (freshMeshPredictedClearanceFloor_le_actual segment request.endpoint
          remaining)

theorem freshMeshClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    forall (current : Endpoint) (requests : List StepRequest),
      0 < FreshMeshClearanceFloor segment current requests
  | current, [] => by
      change (0 : Coordinate) < 1
      decide
  | current, request :: remaining => by
      apply lt_min
      · exact canonicalPredictedClearanceFloor_positive segment current request
      · exact freshMeshClearanceFloor_positive segment request.endpoint
          remaining

theorem meshClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    forall requests : List StepRequest,
      0 < MeshClearanceFloor segment current owner requests
  | [] => by
      change (0 : Coordinate) < 1
      decide
  | request :: remaining => by
      apply lt_min
      · exact (prepared segment current owner request).track.initial.clearance.positive
      · exact freshMeshClearanceFloor_positive segment request.endpoint
          remaining

/-- A single strict bound below the finite tail-clearance minimum discharges
all owner-independent mesh checks. -/
theorem freshMeshSafe_of_edgeVariationBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    forall (current : Endpoint) (requests : List StepRequest)
      (bound : Coordinate),
      CCL.Riemann.ClearSheetContinuation.Subdivision.EdgeVariationBound
          segment bound current (requestEndpoints requests) ->
        bound < FreshMeshClearanceFloor segment current requests ->
          FreshMeshSafe segment current requests
  | _current, [], _bound, _edgeBound, _below => trivial
  | current, request :: remaining, bound, edgeBound, below => by
      change current.parameter <= request.endpoint.parameter /\
        CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <= bound /\
          CCL.Riemann.ClearSheetContinuation.Subdivision.EdgeVariationBound
            segment bound request.endpoint (requestEndpoints remaining) at edgeBound
      change bound < min
        (canonicalPredictedClearanceFloor segment current request)
        (FreshMeshClearanceFloor segment request.endpoint remaining) at below
      exact
        ⟨edgeBound.1,
          edgeBound.2.1.trans_lt (below.trans_le (min_le_left _ _)),
          freshMeshSafe_of_edgeVariationBound segment request.endpoint
            remaining bound edgeBound.2.2
              (below.trans_le (min_le_right _ _))⟩

/-- A single strict bound below the complete finite clearance minimum
discharges the supplied-owner first edge and every canonical tail edge. -/
theorem meshSafe_of_edgeVariationBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest) (bound : Coordinate)
    (edgeBound :
      CCL.Riemann.ClearSheetContinuation.Subdivision.EdgeVariationBound
        segment bound current (requestEndpoints requests))
    (below : bound < MeshClearanceFloor segment current owner requests) :
    MeshSafe segment current owner requests := by
  cases requests with
  | nil => trivial
  | cons request remaining =>
      change current.parameter <= request.endpoint.parameter /\
        CCL.Riemann.ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <= bound /\
          CCL.Riemann.ClearSheetContinuation.Subdivision.EdgeVariationBound
            segment bound request.endpoint (requestEndpoints remaining) at edgeBound
      change bound < min
        (prepared segment current owner request).track.initial.clearance.bound
        (FreshMeshClearanceFloor segment request.endpoint remaining) at below
      exact
        ⟨edgeBound.1,
          edgeBound.2.1.trans_lt (below.trans_le (min_le_left _ _)),
          freshMeshSafe_of_edgeVariationBound segment request.endpoint
            remaining bound edgeBound.2.2
              (below.trans_le (min_le_right _ _))⟩

theorem trySteps_endpoint {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests = some subdivision) :
    subdivision.endpoint = finalTarget left requests := by
  induction requests generalizing left owner subdivision with
  | nil =>
      simp only [trySteps] at success
      cases success
      rfl
  | cons request remaining inductionHypothesis =>
      simp only [trySteps] at success
      split at success
      next ordered =>
        split at success
        next small =>
          split at success
          next failure => contradiction
          next tail recursiveSuccess =>
            cases success
            exact inductionHypothesis request.endpoint
              (advance segment within left owner request small)
              (subdivision := tail) recursiveSuccess
        next notSmall => contradiction
      next notOrdered => contradiction

theorem trySteps_endpoint_parameter {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests = some subdivision) :
    subdivision.endpoint.parameter = (finalTarget left requests).parameter := by
  exact congrArg (fun endpoint : Endpoint => endpoint.parameter)
    (trySteps_endpoint segment within left owner requests success)

theorem finalTarget_requestEndpoints (current : Endpoint)
    (requests : List StepRequest) :
    CCL.Riemann.ClearSheetContinuation.Subdivision.finalTarget current
        (requestEndpoints requests) =
      finalTarget current requests := by
  induction requests generalizing current with
  | nil => rfl
  | cons request remaining inductionHypothesis =>
      exact inductionHypothesis request.endpoint

/-- Attach one common positive root-box diameter to every endpoint of a
displayed finite mesh. -/
def requestsAtDiameter (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    List Endpoint -> List StepRequest
  | [] => []
  | endpoint :: remaining =>
      { endpoint := endpoint
        rootDiameter := rootDiameter
        rootDiameterPositive := rootDiameterPositive } ::
        requestsAtDiameter rootDiameter rootDiameterPositive remaining

@[simp] theorem requestsAtDiameter_length (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) (endpoints : List Endpoint) :
    (requestsAtDiameter rootDiameter rootDiameterPositive endpoints).length =
      endpoints.length := by
  induction endpoints with
  | nil => rfl
  | cons endpoint remaining inductionHypothesis =>
      simp only [requestsAtDiameter, List.length_cons, inductionHypothesis]

@[simp] theorem requestEndpoints_requestsAtDiameter
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (endpoints : List Endpoint) :
    requestEndpoints
        (requestsAtDiameter rootDiameter rootDiameterPositive endpoints) =
      endpoints := by
  induction endpoints with
  | nil => rfl
  | cons endpoint remaining inductionHypothesis =>
      simp only [requestsAtDiameter, requestEndpoints, inductionHypothesis]

/-- The common preparation floor bounds the complete predicted tail minimum,
independently of the endpoint count. -/
theorem uniformPreparedClearanceFloor_le_freshRequests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    forall (current : Endpoint) (endpoints : List Endpoint),
      uniformPreparedClearanceFloor segment rootDiameter <=
        FreshMeshPredictedClearanceFloor segment current
          (requestsAtDiameter rootDiameter rootDiameterPositive endpoints)
  | _current, [] => min_le_right _ _
  | current, endpoint :: remaining => by
      simp only [requestsAtDiameter, FreshMeshPredictedClearanceFloor]
      apply le_min
      · unfold canonicalPredictedClearanceFloor
          canonicalPredictedClearance preparedClearanceLower
        rw [min_self]
        exact uniformPreparedClearanceFloor_le_predicted segment rootDiameter
      · exact uniformPreparedClearanceFloor_le_freshRequests segment
          rootDiameter rootDiameterPositive endpoint remaining

/-- The same floor bounds the supplied-owner first edge and every canonical
tail edge of a common-diameter request list. -/
theorem uniformPreparedClearanceFloor_le_meshRequests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    forall endpoints : List Endpoint,
      uniformPreparedClearanceFloor segment rootDiameter <=
        MeshPredictedClearanceFloor segment current owner
          (requestsAtDiameter rootDiameter rootDiameterPositive endpoints)
  | [] => min_le_right _ _
  | endpoint :: remaining => by
      simp only [requestsAtDiameter, MeshPredictedClearanceFloor]
      apply le_min
      · exact uniformPreparedClearanceFloor_le_predicted segment rootDiameter
      · exact uniformPreparedClearanceFloor_le_freshRequests segment
          rootDiameter rootDiameterPositive endpoint remaining

def dyadicRequests (depth : Nat) (left right : Endpoint)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    List StepRequest :=
  requestsAtDiameter rootDiameter rootDiameterPositive
    (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth left
      right)

@[simp] theorem requestEndpoints_dyadicRequests
    (depth : Nat) (left right : Endpoint)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    requestEndpoints
        (dyadicRequests depth left right rootDiameter rootDiameterPositive) =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth left
        right := by
  simp only [dyadicRequests, requestEndpoints_requestsAtDiameter]

/-- The single positive rational clearance minimum for a complete prepared
dyadic mesh. -/
def dyadicMeshClearanceFloor {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : Coordinate :=
  MeshClearanceFloor segment left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

theorem dyadicMeshClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    0 < dyadicMeshClearanceFloor segment left right owner depth rootDiameter
      rootDiameterPositive :=
  meshClearanceFloor_positive segment left owner _

/-- The completely a-priori clearance minimum for a prepared dyadic mesh. -/
def dyadicMeshPredictedClearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : Coordinate :=
  MeshPredictedClearanceFloor segment left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

theorem dyadicMeshPredictedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    0 < dyadicMeshPredictedClearanceFloor segment left right owner depth
      rootDiameter rootDiameterPositive :=
  meshPredictedClearanceFloor_positive segment left owner _

theorem uniformPreparedClearanceFloor_le_dyadicPredicted
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    uniformPreparedClearanceFloor segment rootDiameter <=
      dyadicMeshPredictedClearanceFloor segment left right owner depth
        rootDiameter rootDiameterPositive := by
  unfold dyadicMeshPredictedClearanceFloor dyadicRequests
  exact uniformPreparedClearanceFloor_le_meshRequests segment left owner
    rootDiameter rootDiameterPositive _

theorem dyadicMeshPredictedClearanceFloor_le_actual
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    dyadicMeshPredictedClearanceFloor segment left right owner depth
        rootDiameter rootDiameterPositive ≤
      dyadicMeshClearanceFloor segment left right owner depth rootDiameter
        rootDiameterPositive :=
  meshPredictedClearanceFloor_le_actual segment left owner _

/-- Total prepared checker for the same depth-`n` dyadic endpoint mesh used
by the pure geometric path. -/
def tryDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    Option (Subdivision segment within left owner) :=
  trySteps segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

/-- Exact success evidence for the displayed dyadic checker, retaining the
actually transported owner at every recursive edge. -/
def ExecutedDyadicMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : Prop :=
  ExecutedMeshSafe segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

instance executedDyadicMeshSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    Decidable (ExecutedDyadicMeshSafe segment within left right owner depth
      rootDiameter rootDiameterPositive) :=
  executedMeshSafeDecidable segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

/-- Rebuild the successful dyadic subdivision from erased exact-comparison
evidence, without rerunning those comparisons at runtime. -/
def ofExecutedDyadicMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : ExecutedDyadicMeshSafe segment within left right owner depth
      rootDiameter rootDiameterPositive) :
    Subdivision segment within left owner :=
  ofExecutedMeshSafe segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive) safe

/-- Exact executed-mesh evidence reconstructs precisely the successful
ordinary dyadic-checker result. -/
theorem tryDyadic_eq_some_ofExecutedDyadicMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : ExecutedDyadicMeshSafe segment within left right owner depth
      rootDiameter rootDiameterPositive) :
    tryDyadic segment within left right owner depth rootDiameter
        rootDiameterPositive =
      some (ofExecutedDyadicMeshSafe segment within left right owner depth
        rootDiameter rootDiameterPositive safe) := by
  unfold tryDyadic ofExecutedDyadicMeshSafe
  exact trySteps_eq_some_ofExecutedMeshSafe segment within _ safe

/-- Every accepted prepared dyadic subdivision has exactly the retained-edge
presentation of the owner-independent dyadic mesh. -/
theorem tryDyadic_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth rootDiameter
      rootDiameterPositive = some subdivision) :
    subdivision.parameterEdges =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicEdges depth left
        right := by
  have edges := trySteps_parameterEdges segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive) success
  rw [requestEndpoints_dyadicRequests,
    CCL.Riemann.ClearSheetContinuation.Subdivision.parameterEdgesFrom_dyadicTargets]
    at edges
  exact edges

/-- A successful dyadic checker retains the canonical endpoint-and-diameter
request list, not merely its parameter edges. -/
theorem tryDyadic_requests
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth rootDiameter
      rootDiameterPositive = some subdivision) :
    subdivision.requests =
      dyadicRequests depth left right rootDiameter rootDiameterPositive := by
  exact trySteps_requests segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive) success

/-- Finite, sheet-independent acceptance condition for one prepared dyadic
mesh.  It consists entirely of rational order and clearance comparisons. -/
def DyadicMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : Prop :=
  MeshSafe segment left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive)

/-- One rational inequality between the exact dyadic variation modulus and
the computed finite clearance minimum proves the complete dependent mesh
safe. -/
theorem dyadicMeshSafe_of_variation_lt_clearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter)
    (below :
      CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.ClearSheetContinuation.variationBound segment
            left.parameter right.parameter) depth <
        dyadicMeshClearanceFloor segment left right owner depth rootDiameter
          rootDiameterPositive) :
    DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive := by
  unfold DyadicMeshSafe
  apply meshSafe_of_edgeVariationBound segment left owner _ _
  · rw [requestEndpoints_dyadicRequests]
    exact
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_edgeVariationBound
        segment depth left right ordered
  · exact below

/-- The dyadic mesh is safe already from comparison with the explicit
predicted Newton-clearance minimum; no post-extraction clearance value occurs
in this hypothesis. -/
theorem dyadicMeshSafe_of_variation_lt_predictedClearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter)
    (below :
      CCL.FiniteGeometric.quarterRadius
          (CCL.Riemann.ClearSheetContinuation.variationBound segment
            left.parameter right.parameter) depth <
        dyadicMeshPredictedClearanceFloor segment left right owner depth
          rootDiameter rootDiameterPositive) :
    DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive :=
  dyadicMeshSafe_of_variation_lt_clearanceFloor segment left right owner depth
    rootDiameter rootDiameterPositive ordered
    (below.trans_le
      (dyadicMeshPredictedClearanceFloor_le_actual segment left right owner
        depth rootDiameter rootDiameterPositive))

/-- Explicit finite refinement depth obtained from the path-wide preparation
floor.  It does not inspect any intermediate owner or extraction result. -/
def sufficientDyadicDepth
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint) (rootDiameter : Coordinate) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow
    (CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter right.parameter)
    0 (uniformPreparedClearanceFloor segment rootDiameter)

theorem sufficientDyadicDepth_variation_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint) {rootDiameter : Coordinate}
    (rootDiameterPositive : 0 < rootDiameter) :
    CCL.FiniteGeometric.quarterRadius
        (CCL.Riemann.ClearSheetContinuation.variationBound segment
          left.parameter right.parameter)
        (sufficientDyadicDepth segment left right rootDiameter) <
      uniformPreparedClearanceFloor segment rootDiameter := by
  exact CCL.FiniteGeometric.firstQuarterBelow_accurate _
    (CCL.Riemann.ClearSheetContinuation.variationBound_nonneg segment
      left.parameter right.parameter)
    0 _ (uniformPreparedClearanceFloor_positive segment rootDiameterPositive)

/-- The explicit depth always yields a safe prepared mesh. -/
theorem sufficientDyadicMeshSafe
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter) :
    DyadicMeshSafe segment left right owner
      (sufficientDyadicDepth segment left right rootDiameter) rootDiameter
        rootDiameterPositive := by
  apply dyadicMeshSafe_of_variation_lt_predictedClearanceFloor segment left
    right owner (sufficientDyadicDepth segment left right rootDiameter)
      rootDiameter rootDiameterPositive ordered
  exact (sufficientDyadicDepth_variation_lt segment left right
      rootDiameterPositive).trans_le
    (uniformPreparedClearanceFloor_le_dyadicPredicted segment left right owner
      (sufficientDyadicDepth segment left right rootDiameter) rootDiameter
        rootDiameterPositive)

/-- Every later dyadic depth is also safe.  This lets finitely many segments
share the maximum of their individually computed sufficient depths. -/
theorem dyadicMeshSafe_of_sufficientDepth_le
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter)
    (enough : sufficientDyadicDepth segment left right rootDiameter <= depth) :
    DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive := by
  apply dyadicMeshSafe_of_variation_lt_predictedClearanceFloor segment left
    right owner depth rootDiameter rootDiameterPositive ordered
  have laterLe := CCL.FiniteGeometric.quarterRadius_antitone
    (CCL.Riemann.ClearSheetContinuation.variationBound_nonneg segment
      left.parameter right.parameter) enough
  exact (laterLe.trans_lt
      (sufficientDyadicDepth_variation_lt segment left right
        rootDiameterPositive)).trans_le
    (uniformPreparedClearanceFloor_le_dyadicPredicted segment left right owner
      depth rootDiameter rootDiameterPositive)

instance dyadicMeshSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) :
    Decidable (DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive) := by
  unfold DyadicMeshSafe
  infer_instance

/-- Boolean form of the complete finite dyadic mesh check. -/
def dyadicMeshAccepted {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter) : Bool :=
  decide (DyadicMeshSafe segment left right owner depth rootDiameter
    rootDiameterPositive)

theorem dyadicMeshSafe_of_accepted
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (accepted : dyadicMeshAccepted segment left right owner depth rootDiameter
      rootDiameterPositive = true) :
    DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive :=
  of_decide_eq_true accepted

/-- The dependent prepared subdivision computed directly from a verified
finite dyadic mesh condition. -/
def checkedDyadic {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive) : Subdivision segment within left owner :=
  ofMeshSafe segment within left owner
    (dyadicRequests depth left right rootDiameter rootDiameterPositive) safe

/-- Total prepared dyadic subdivision at the explicit sufficient depth. -/
def sufficientDyadic
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter) :
    Subdivision segment within left owner :=
  checkedDyadic segment within left right owner
    (sufficientDyadicDepth segment left right rootDiameter) rootDiameter
      rootDiameterPositive
      (sufficientDyadicMeshSafe segment left right owner rootDiameter
        rootDiameterPositive ordered)

/-- A verified finite rational mesh condition is sufficient for the existing
executable checker to succeed with the directly constructed subdivision. -/
theorem tryDyadic_eq_some_checkedDyadic
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    (safe : DyadicMeshSafe segment left right owner depth rootDiameter
      rootDiameterPositive) :
    tryDyadic segment within left right owner depth rootDiameter
        rootDiameterPositive =
      some (checkedDyadic segment within left right owner depth rootDiameter
        rootDiameterPositive safe) :=
  trySteps_eq_some_ofMeshSafe segment within left owner _ safe

theorem tryDyadic_sufficient_eq_some
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (ordered : left.parameter <= right.parameter) :
    tryDyadic segment within left right owner
        (sufficientDyadicDepth segment left right rootDiameter) rootDiameter
          rootDiameterPositive =
      some (sufficientDyadic segment within left right owner rootDiameter
        rootDiameterPositive ordered) :=
  tryDyadic_eq_some_checkedDyadic segment within left right owner
    (sufficientDyadicDepth segment left right rootDiameter) rootDiameter
      rootDiameterPositive
      (sufficientDyadicMeshSafe segment left right owner rootDiameter
        rootDiameterPositive ordered)

theorem tryDyadic_stepCount {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth rootDiameter
      rootDiameterPositive = some subdivision) :
    subdivision.stepCount = 2 ^ depth := by
  exact (trySteps_stepCount segment within left owner _ success).trans (by
    simp only [dyadicRequests, requestsAtDiameter_length,
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_length])

theorem tryDyadic_endpoint {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth rootDiameter
      rootDiameterPositive = some subdivision) :
    subdivision.endpoint = right := by
  calc
    subdivision.endpoint =
        finalTarget left
          (dyadicRequests depth left right rootDiameter
            rootDiameterPositive) :=
      trySteps_endpoint segment within left owner _ success
    _ = CCL.Riemann.ClearSheetContinuation.Subdivision.finalTarget left
          (requestEndpoints
            (dyadicRequests depth left right rootDiameter
              rootDiameterPositive)) :=
      (finalTarget_requestEndpoints left _).symm
    _ = right := by
      simp only [requestEndpoints_dyadicRequests,
        CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_finalTarget]

def toClearPath {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))} :
    (subdivision : Subdivision segment within left owner) ->
      ClearPath polynomial ambient (segment.pointAt left.parameter)
        (segment.pointAt subdivision.endpoint.parameter)
  | .stop left _ => .nil (segment.pointAt left.parameter)
  | .next left _ request _ _ _ remaining =>
      .cons
        (segment.restrict within left.parameter request.endpoint.parameter
          left.inside request.endpoint.inside)
        remaining.toClearPath

/-- The terminal endpoint of any cached subdivision is determined solely by
the displayed right endpoints of its accepted parameter edges. -/
theorem endpoint_eq_finalTarget_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.endpoint =
      CCL.Riemann.ClearSheetContinuation.Subdivision.finalTarget left
        (subdivision.parameterEdges.map (fun edge => edge.right)) := by
  induction subdivision with
  | stop => rfl
  | next current owner request cached ordered small remaining
      inductionHypothesis =>
      simpa only [endpoint, parameterEdges, List.map_cons,
        CCL.Riemann.ClearSheetContinuation.Subdivision.finalTarget] using
          inductionHypothesis

/-- Forgetting owner data from an arbitrary cached subdivision yields exactly
the geometric path through its stored parameter edges. -/
theorem toClearPath_eq_geometricPath_parameterEdges
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.toClearPath.castFinish
        (congrArg (fun endpoint : Endpoint =>
          segment.pointAt endpoint.parameter)
            (endpoint_eq_finalTarget_parameterEdges subdivision)) =
      CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
        within left
          (subdivision.parameterEdges.map (fun edge => edge.right)) := by
  induction subdivision with
  | stop => rfl
  | next current owner request cached ordered small remaining
      inductionHypothesis =>
      simp only [toClearPath, endpoint, parameterEdges, List.map_cons,
        CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath,
        ClearPath.castFinish_cons]
      exact congrArg
        (ClearPath.cons
          (segment.restrict within current.parameter
            request.endpoint.parameter current.inside
              request.endpoint.inside)) inductionHypothesis

theorem castOwner_toClearPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second)
    (subdivision : Subdivision segment within left first) :
    (subdivision.castOwner equal).toClearPath.castFinish
        (congrArg (fun endpoint : Endpoint =>
          segment.pointAt endpoint.parameter)
          (castOwner_endpoint equal subdivision)) =
      subdivision.toClearPath := by
  cases equal
  rfl

@[simp] theorem nextCached_toClearPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (ordered : left.parameter <= request.endpoint.parameter)
    (cachedSmall : CCL.Riemann.ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall :
      CCL.Riemann.ClearSheetContinuation.variationBound segment
        left.parameter request.endpoint.parameter <
          (prepared segment left owner request).track.initial.clearance.bound)
    (remaining : Subdivision segment within request.endpoint
      (advanceCached segment within left owner request cached cachedSmall)) :
    (nextCached segment within left owner request cached ordered cachedSmall
      canonicalSmall remaining).toClearPath.castFinish
        (congrArg (fun endpoint : Endpoint =>
          segment.pointAt endpoint.parameter)
          (nextCached_endpoint segment within left owner request cached ordered
            cachedSmall canonicalSmall remaining)) =
        .cons
          (segment.restrict within left.parameter request.endpoint.parameter
            left.inside request.endpoint.inside)
          remaining.toClearPath := by
  unfold nextCached
  simp only [toClearPath, endpoint, ClearPath.castFinish_cons]
  apply congrArg (ClearPath.cons
    (segment.restrict within left.parameter request.endpoint.parameter
      left.inside request.endpoint.inside))
  exact castOwner_toClearPath
    (advanceCached_eq_advance segment within left owner request cached
      cachedSmall canonicalSmall) remaining

/-- A successful prepared check follows exactly the owner-independent clear
path through the same displayed request endpoints. -/
theorem trySteps_toClearPath_eq_geometricPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (requests : List StepRequest)
    {subdivision : Subdivision segment within left owner}
    (success : trySteps segment within left owner requests = some subdivision) :
    subdivision.toClearPath.castFinish
        (congrArg (fun endpoint : Endpoint =>
          segment.pointAt endpoint.parameter)
            ((trySteps_endpoint segment within left owner requests
              success).trans
                (finalTarget_requestEndpoints left requests).symm)) =
      CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
        within left (requestEndpoints requests) := by
  induction requests generalizing left owner subdivision with
  | nil =>
      simp only [trySteps] at success
      cases success
      rfl
  | cons request remaining inductionHypothesis =>
      simp only [trySteps] at success
      split at success
      next ordered =>
        split at success
        next small =>
          split at success
          next failure => contradiction
          next tail recursiveSuccess =>
            cases success
            let cached := CachedSource.canonical segment left owner request
            let canonicalSmall :
                CCL.Riemann.ClearSheetContinuation.variationBound segment
                    left.parameter request.endpoint.parameter <
                  (prepared segment left owner request).track.initial.clearance.bound :=
              small
            let nextOwner := advanceCached segment within left owner request
              cached small
            let computed := nextCached segment within left owner request cached
              ordered small canonicalSmall tail
            let endpointEqual := congrArg (fun endpoint : Endpoint =>
                segment.pointAt endpoint.parameter)
              (nextCached_endpoint segment within left owner request cached
                ordered small canonicalSmall tail)
            let tailEqual := congrArg (fun endpoint : Endpoint =>
                segment.pointAt endpoint.parameter)
              ((trySteps_endpoint segment within request.endpoint nextOwner
                  remaining recursiveSuccess).trans
                (finalTarget_requestEndpoints request.endpoint remaining).symm)
            change computed.toClearPath.castFinish
                (endpointEqual.trans tailEqual) =
              CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath
                segment within left (requestEndpoints (request :: remaining))
            let head := segment.restrict within left.parameter
              request.endpoint.parameter left.inside request.endpoint.inside
            calc
              computed.toClearPath.castFinish
                    (endpointEqual.trans tailEqual) =
                  (computed.toClearPath.castFinish endpointEqual).castFinish
                    tailEqual :=
                (ClearPath.castFinish_castFinish computed.toClearPath
                  endpointEqual tailEqual).symm
              _ = (ClearPath.cons head tail.toClearPath).castFinish
                    tailEqual := by
                exact congrArg (fun path => path.castFinish tailEqual)
                  (nextCached_toClearPath segment within left owner request
                    cached ordered small canonicalSmall tail)
              _ = ClearPath.cons head
                    (tail.toClearPath.castFinish tailEqual) :=
                ClearPath.castFinish_cons head tail.toClearPath tailEqual
              _ = ClearPath.cons head
                    (CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath
                      segment within request.endpoint
                        (requestEndpoints remaining)) := by
                exact congrArg (ClearPath.cons head)
                  (inductionHypothesis request.endpoint nextOwner
                    (subdivision := tail) recursiveSuccess)
              _ = CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath
                    segment within left
                      (requestEndpoints (request :: remaining)) := rfl
        next notSmall => contradiction
      next notOrdered => contradiction

/-- A successful prepared dyadic check has exactly the owner-independent
dyadic clear path selected by the same finite endpoint mesh. -/
theorem tryDyadic_toClearPath_eq_dyadicPath
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left right : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (depth : Nat) (rootDiameter : Coordinate)
    (rootDiameterPositive : 0 < rootDiameter)
    {subdivision : Subdivision segment within left owner}
    (success : tryDyadic segment within left right owner depth rootDiameter
      rootDiameterPositive = some subdivision) :
    subdivision.toClearPath.castFinish
        (congrArg (fun endpoint : Endpoint =>
          segment.pointAt endpoint.parameter)
            (tryDyadic_endpoint segment within left right owner depth
              rootDiameter rootDiameterPositive success)) =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicPath segment within
        depth left right := by
  let requests :=
    dyadicRequests depth left right rootDiameter rootDiameterPositive
  have mesh := trySteps_toClearPath_eq_geometricPath segment within left owner
    requests success
  let endpointsEqual : requestEndpoints requests =
      CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth left
        right :=
    requestEndpoints_dyadicRequests depth left right rootDiameter
      rootDiameterPositive
  let requestsFinishEqual := congrArg
    (fun endpoints : List Endpoint =>
      segment.pointAt
        ((CCL.Riemann.ClearSheetContinuation.Subdivision.finalTarget left
          endpoints).parameter)) endpointsEqual
  let targetsFinishEqual := congrArg
    (fun endpoint : Endpoint => segment.pointAt endpoint.parameter)
      (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets_finalTarget
        depth left right)
  have transportGeometry : forall (first second : List Endpoint)
      (equal : first = second),
      (CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
        within left first).castFinish
          (congrArg
            (fun endpoints : List Endpoint =>
              segment.pointAt
                ((CCL.Riemann.ClearSheetContinuation.Subdivision.finalTarget
                  left endpoints).parameter)) equal) =
        CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
          within left second := by
    intro first second equal
    subst second
    rfl
  have geometricEqual :
      (CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
        within left (requestEndpoints requests)).castFinish
          requestsFinishEqual =
        CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
          within left
            (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth
              left right) := by
    exact transportGeometry _ _ endpointsEqual
  calc
    subdivision.toClearPath.castFinish
          (congrArg (fun endpoint : Endpoint =>
            segment.pointAt endpoint.parameter)
              (tryDyadic_endpoint segment within left right owner depth
                rootDiameter rootDiameterPositive success)) =
        ((subdivision.toClearPath.castFinish
          (congrArg (fun endpoint : Endpoint =>
            segment.pointAt endpoint.parameter)
              ((trySteps_endpoint segment within left owner requests
                success).trans
                  (finalTarget_requestEndpoints left requests).symm))).castFinish
            requestsFinishEqual).castFinish targetsFinishEqual := by
      simp only [ClearPath.castFinish_castFinish]
    _ = ((CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
          within left (requestEndpoints requests)).castFinish
            requestsFinishEqual).castFinish targetsFinishEqual := by
      rw [mesh]
    _ = (CCL.Riemann.ClearSheetContinuation.Subdivision.geometricPath segment
          within left
            (CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicTargets depth
              left right)).castFinish targetsFinishEqual := by
      rw [geometricEqual]
    _ = CCL.Riemann.ClearSheetContinuation.Subdivision.dyadicPath segment within
          depth left right := rfl

@[simp] theorem toClearPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    (subdivision : Subdivision segment within left owner) :
    subdivision.toClearPath.segmentCount = subdivision.stepCount := by
  induction subdivision with
  | stop => rfl
  | next left owner request cached ordered small remaining inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end Subdivision

end CCL.Riemann.PreparedSheetContinuation
