module

public import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Two original fixed root boxes on one actual prepared edge

The stored accepted variation pays a fixed-box budget on the exact cached
prepared source Owner. A separately retained original budget supplies its
own whole-edge geometric movement certificate. The same actual affine
points and original polynomial define a two-budget PathData; the existing
finite comparison procedure then transports a starting comparison to the
actual transported target Owner. No new integration subdivision, source
preparation, endpoint isolation or assumed finish relation is introduced.
-/

public section

namespace Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (PathData Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_initial_box)

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    (edge : PreparedEdge curve differential)

/-- The accepted edge variation pays the literal cached prepared source Owner's contour. -/
private theorem cached_small :
    edge.radicandMovementBound < edge.cached.preparedOwner.track.initial.clearance.bound := by
  rewrite [edge.cached.preparedOwner_eq]
  exact edge.small

/-- Construct a fixed-box budget on the already retained prepared source using its actual accepted variation. -/
def rootBudget : FixedRootBoxBudget.Budget edge.cached.preparedOwner :=
  FixedRootBoxBudget.Budget.acquire edge.cached.preparedOwner edge.radicandMovementBound
    edge.radicandMovementBound_nonnegative edge.cached_small

/-- The local root budget retains the original accepted edge's exact variation bound. -/
theorem rootBudget_movement : edge.rootBudget.movement = edge.radicandMovementBound := by rfl

/-- The original physical box Lipschitz bound and exact affine displacement determine a squared path scale. -/
@[expose] def radicandScale : Rational :=
  Bounds.Box.denseLipschitzBound curve.polynomial edge.ambient * edge.pointMovement

/-- The same physical Lipschitz bound and endpoint quadrance make this scale nonnegative. -/
theorem radicandScale_nonnegative : 0 ≤ edge.radicandScale :=
  Order.Arithmetic.mul_nonneg_direct (Bounds.Box.denseLipschitzBound_pos curve.polynomial edge.ambient).le
    (Norm.Basic.normSq_nonneg (edge.point 1 - edge.point 0))

/-- The actual polynomial values on the same affine edge satisfy the computed squared path scale. -/
private theorem radicand_variation (first last : Rational) (firstInside : Inside first) (lastInside : Inside last) :
    Norm.Basic.normSq (curve.polynomial.eval (edge.point first) - curve.polynomial.eval (edge.point last)) ≤
      edge.radicandScale * (last - first) ^ 2 := by
  have bounded := Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound curve.polynomial
    (edge.point_contains first firstInside) (edge.point_contains last lastInside)
  have distance := edge.localSegment.normSq_pointAt_sub_pointAt first last
  change Norm.Basic.normSq (edge.point first - edge.point last) =
    (first - last) ^ 2 * Norm.Basic.normSq
      (edge.segment.pointAt edge.request.endpoint.parameter - edge.segment.pointAt edge.left.parameter) at distance
  rewrite [← edge.pointMovement_eq_parameterEdge] at distance
  exact bounded.trans_eq (by
    rewrite [distance]
    unfold radicandScale
    ring1)

variable {source : Canonical} {owner : Owner source}
    (second : FixedRootBoxBudget.Budget owner)
    (movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (source - curve.polynomial.eval (edge.point time)) ≤ second.movement)

/-- Construct two-budget path data on the actual accepted affine edge and the original polynomial.

The first complete budget is an already retained execution of rootBudget.
The second budget and its geometric whole-edge movement are independent
inputs. The accepted edge and finite physical Lipschitz bound supply every
remaining PathData condition internally.
-/
def rootPathData (first : FixedRootBoxBudget.Budget edge.cached.preparedOwner)
    (first_eq : first = edge.rootBudget) : PathData first second :=
  { point := fun time => curve.polynomial.eval (edge.point time)
    nonzero := fun time inside => edge.localSegment.pointAt_eval_ne_zero time inside
    firstMovement := fun time inside => by
      have bounded := edge.radicandDifference_le time inside
      rewrite [edge.point_zero] at bounded
      rewrite [Norm.Basic.normSq_eq_canonical] at bounded
      rewrite [first_eq, edge.rootBudget_movement]
      exact bounded
    secondMovement := fun time inside => by
      have bounded := movement time inside
      rewrite [Norm.Basic.normSq_eq_canonical] at bounded
      exact bounded
    scale := edge.radicandScale
    scale_nonnegative := edge.radicandScale_nonnegative
    variation := fun first last firstInside lastInside => by
      have bounded := edge.radicand_variation first last firstInside lastInside
      rewrite [Norm.Basic.normSq_eq_canonical] at bounded
      exact bounded }

/-- The two-box path reads the literal actual edge polynomial at each exact original affine fraction. -/
theorem rootPathData_point (first : FixedRootBoxBudget.Budget edge.cached.preparedOwner)
    (first_eq : first = edge.rootBudget) (time : Rational) :
    (edge.rootPathData second movement first first_eq).point time = curve.polynomial.eval (edge.point time) := by rfl

/-- One cached local budget and its complete two-original-budget path construction.

The whole factory equations retain the already accepted edge, both
original Owner indices, the computed local majorant and both positive
clearances. A later comparison consumes these exact caches without
rebuilding a source or replaying the integration subdivision.
-/
@[expose] def RootPath :=
  (first : { budget : FixedRootBoxBudget.Budget edge.cached.preparedOwner // budget = edge.rootBudget }) ×
  { path : PathData first.val second // path = edge.rootPathData second movement first.val first.property }

namespace RootPath

variable {edge second movement}

/-- Cache the original accepted-edge budget and its actual two-budget PathData once. -/
def build (edge : PreparedEdge curve differential) (second : FixedRootBoxBudget.Budget owner)
    (movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (source - curve.polynomial.eval (edge.point time)) ≤ second.movement) :
    RootPath edge second movement :=
  let first := edge.rootBudget
  let path := edge.rootPathData second movement first rfl
  ⟨⟨first, rfl⟩, ⟨path, rfl⟩⟩

variable (retained : RootPath edge second movement)

/-- Read the already cached local budget on the SAME actual prepared source Owner. -/
@[expose] def first : FixedRootBoxBudget.Budget edge.cached.preparedOwner := retained.1.val

/-- The complete cached local budget is the original accepted-edge factory. -/
theorem first_eq : retained.first = edge.rootBudget := retained.1.property

/-- Read the same cached two-budget path, preserving both original budget and Owner indices. -/
@[expose] def path : PathData retained.first second := retained.2.val

/-- The whole cached path is the original actual-edge factory on those SAME two budgets. -/
theorem path_eq : retained.path = edge.rootPathData second movement retained.first retained.first_eq :=
  retained.2.property

/-- Every cached path point remains the literal polynomial value at the original edge fraction. -/
theorem point_eq (time : Rational) : retained.path.point time = curve.polynomial.eval (edge.point time) := by
  rewrite [retained.path_eq]
  exact edge.rootPathData_point second movement retained.first retained.first_eq time

/-- The cached path starts at the original prepared source's exact radicand. -/
theorem source_eq : retained.path.point 0 = curve.polynomial.eval (edge.segment.pointAt edge.left.parameter) :=
  (retained.point_eq 0).trans (congrArg curve.polynomial.eval edge.point_zero)

/-- The cached path ends at the original request endpoint's exact radicand. -/
theorem target_eq : retained.path.point 1 =
    curve.polynomial.eval (edge.segment.pointAt edge.request.endpoint.parameter) :=
  (retained.point_eq 1).trans (congrArg curve.polynomial.eval edge.point_one)

/-- Transport the actual starting comparison to the supplied original transported target and independent reference.

Only exact endpoint indices are transported. The moving Owner is retained
with its full original factory equation; its own prepared-box refinement
is derived from reservedTransport. The supplied reference endpoints keep
their separate refinements to the second original box. Starting agreement
is composed with the actual source-preparation comparison. The existing
finite fixed-box path comparison derives the finishing agreement.
-/
def finishEquivalent
    (firstReference : Owner (curve.polynomial.eval (edge.segment.pointAt edge.left.parameter)))
    (firstRefines : firstReference.track.initial.box.Refines owner.track.initial.box)
    (lastReference : Owner (curve.polynomial.eval (edge.segment.pointAt edge.request.endpoint.parameter)))
    (lastRefines : lastReference.track.initial.box.Refines owner.track.initial.box)
    (start : NamedEquivalent (ownerRootName edge.owner.parameterNonzero edge.owner)
      (ownerRootName firstReference.parameterNonzero firstReference))
    (moving : Owner (curve.polynomial.eval (edge.segment.pointAt edge.request.endpoint.parameter)))
    (moving_eq : moving = PreparedSheetContinuation.transported edge.segment edge.within edge.left
      edge.owner edge.request edge.small) :
    NamedEquivalent (ownerRootName moving.parameterNonzero moving)
      (ownerRootName lastReference.parameterNonzero lastReference) := by
  let preparedStart := castOwnerParameter retained.source_eq.symm edge.cached.preparedOwner
  let referenceStart := castOwnerParameter retained.source_eq.symm firstReference
  let preparedFinish := castOwnerParameter retained.target_eq.symm moving
  let referenceFinish := castOwnerParameter retained.target_eq.symm lastReference
  have sourcePrepared := PreparedSheetContinuation.sourceRootEquivalent edge.segment edge.left edge.owner edge.request
  have cachedPrepared : NamedEquivalent (ownerRootName edge.owner.parameterNonzero edge.owner)
      (ownerRootName edge.cached.preparedOwner.parameterNonzero edge.cached.preparedOwner) := by
    rewrite [edge.cached.preparedOwner_eq]
    exact sourcePrepared
  have initial : NamedEquivalent (ownerRootName preparedStart.parameterNonzero preparedStart)
      (ownerRootName referenceStart.parameterNonzero referenceStart) :=
    NamedEquivalent.transport
      (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter retained.source_eq.symm
        edge.cached.preparedOwner).symm
      (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter retained.source_eq.symm firstReference).symm
      (cachedPrepared.symm.trans start)
  have movedRefines : moving.track.initial.box.Refines edge.cached.preparedOwner.track.initial.box := by
    rewrite [moving_eq, edge.cached.preparedOwner_eq]
    exact RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines
      (PreparedSheetContinuation.prepared edge.segment edge.left edge.owner edge.request)
      (edge.segment.pointAt_eval_ne_zero edge.request.endpoint.parameter edge.request.endpoint.inside) _
      (PreparedSheetContinuation.transportReserve edge.segment edge.left edge.request)
  have compared := retained.path.retainedEquivalent preparedStart referenceStart
    (by rewrite [castOwnerParameter_initial_box]; exact Geometry.Rational.Box.refines_refl _)
    (by rewrite [castOwnerParameter_initial_box]; exact firstRefines)
    initial preparedFinish referenceFinish
    (by rewrite [castOwnerParameter_initial_box]; exact movedRefines)
    (by rewrite [castOwnerParameter_initial_box]; exact lastRefines)
  exact NamedEquivalent.transport
    (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter retained.target_eq.symm moving)
    (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter retained.target_eq.symm lastReference) compared

/-- Compare the actual retained advancement with its independent fixed-box endpoint reference.

The original moving Owner and original retained tail Owner are supplied
with their whole factory equations. The original reserve-retention
comparison composes with finishEquivalent; no assumed tail agreement or
second advancement is requested from the consumer.
-/
def advanceEquivalent
    (firstReference : Owner (curve.polynomial.eval (edge.segment.pointAt edge.left.parameter)))
    (firstRefines : firstReference.track.initial.box.Refines owner.track.initial.box)
    (lastReference : Owner (curve.polynomial.eval (edge.segment.pointAt edge.request.endpoint.parameter)))
    (lastRefines : lastReference.track.initial.box.Refines owner.track.initial.box)
    (start : NamedEquivalent (ownerRootName edge.owner.parameterNonzero edge.owner)
      (ownerRootName firstReference.parameterNonzero firstReference))
    (moving : Owner (curve.polynomial.eval (edge.segment.pointAt edge.request.endpoint.parameter)))
    (moving_eq : moving = PreparedSheetContinuation.transported edge.segment edge.within edge.left
      edge.owner edge.request edge.small)
    (advanced : Owner (curve.polynomial.eval (edge.segment.pointAt edge.request.endpoint.parameter)))
    (advanced_eq : advanced = PreparedSheetContinuation.advance edge.segment edge.within edge.left
      edge.owner edge.request edge.small) :
    NamedEquivalent (ownerRootName advanced.parameterNonzero advanced)
      (ownerRootName lastReference.parameterNonzero lastReference) := by
  have compared := retained.finishEquivalent firstReference firstRefines lastReference lastRefines start
    moving moving_eq
  have kept := PreparedSheetContinuation.retainedAtReserveRootEquivalent moving
    (PreparedSheetContinuation.preparedClearanceLower edge.segment edge.left edge.request)
  have kept_eq : PreparedSheetContinuation.retainedAtReserve moving
      (PreparedSheetContinuation.preparedClearanceLower edge.segment edge.left edge.request) = advanced := by
    rewrite [moving_eq, advanced_eq]
    rfl
  have name_eq := congrArg (fun target : Owner
    (curve.polynomial.eval (edge.segment.pointAt edge.request.endpoint.parameter)) =>
      ownerRootName target.parameterNonzero target) kept_eq
  have movingToAdvanced : NamedEquivalent (ownerRootName moving.parameterNonzero moving)
      (ownerRootName advanced.parameterNonzero advanced) := NamedEquivalent.transport rfl name_eq kept
  exact movingToAdvanced.symm.trans compared

end RootPath

end Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge

end
