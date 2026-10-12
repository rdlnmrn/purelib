module
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.Riemann.Branches.ReconditionedClearSheetContinuation
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
public import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Newton.Restart.Separated.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Riemann.RootContinuation.SquareRootContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Power.Gaussian
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

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

namespace Purelib.Riemann.Branches.PreparedSheetContinuation

open Purelib.Data.Rat

open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance

/-- The exact rational coordinate carrier of preparation requests and clearance bounds. -/
public abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
public abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- The original Gaussian polynomial type evaluated along cleared segments. -/
public abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The original rational box carrier with its retained coordinate bounds. -/
public abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root owner indexed by its exact radicand. -/
public abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- A segment parameter retaining its proof of membership in the unit interval. -/
public abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- Operational equivalence of the two original coherent Gaussian names. -/
public abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
/-- The original coherent Gaussian name carrier. -/
public abbrev Named := Purelib.Approximation.Gaussian.Name.Basic.Named

open Purelib.Approximation.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- A successful moving recentering retains the original named square root.

The witness compares both exact owners through a refinement of the retained bridge owner, preserving the original
radicand and root assignment. -/
@[expose] public def movingRecenterRootEquivalent {parameter : Gaussian}
    (source : Owner parameter)
    (reset : ExactQuadraticOwnerClearance.MovingRecenter parameter source) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        source.parameterNonzero source)
      (SquareRootTrackEquivalence.ownerRootName
        source.parameterNonzero reset.owner) := by
  let common := reset.bridgeOwner.refineAt 1
  have commonStrictBridge : common.track.initial.box.StrictInterior
      reset.bridgeOwner.track.initial.box := by
    change
      (reset.bridgeOwner.track.refine reset.bridgeOwner.track.initial
        (Bounds.AccuracyRadius.accuracyRadius
          (CoherentRoot.stepTarget reset.bridgeOwner.track 0))
        (Bounds.AccuracyRadius.accuracyRadius_pos
          (CoherentRoot.stepTarget_positive
            reset.bridgeOwner.track 0))).box.StrictInterior
        reset.bridgeOwner.track.initial.box
    exact reset.bridgeOwner.track.strict _ _ _
  have commonRefinesBridge : common.track.initial.box.Refines
      reset.bridgeOwner.track.initial.box :=
    reset.bridgeOwner.refineAt_initial_refines 1
  have sourceToCommon :=
    SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      source.parameterNonzero source.track common.track
        ((Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines commonStrictBridge)
            reset.bridgeRefinesSource)
  have movedToCommon :=
    SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      source.parameterNonzero reset.owner.track common.track
        ((Geometry.Rational.Box.Refinement.StrictInterior.of_refines reset.bridgeStrictOwner) commonRefinesBridge)
  exact Equivalence.NamedEquivalent.trans sourceToCommon
    movedToCommon.symm

section
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Use the owner returned by moving recentering, retaining the original owner when that attempt fails. -/
@[expose] public def recentered {parameter : Gaussian} (owner : Owner parameter) :
    Owner parameter :=
  match ExactQuadraticOwnerClearance.movingRecenter? owner with
  | none => owner
  | some reset => reset.owner

/-- A successful moving recentering determines the exact owner returned by `recentered`. -/
public theorem recentered_eq_of_movingRecenter_eq_some {parameter : Gaussian}
    (owner : Owner parameter) (reset : ExactQuadraticOwnerClearance.MovingRecenter parameter owner)
    (found : ExactQuadraticOwnerClearance.movingRecenter? owner = some reset) :
    recentered owner = reset.owner := by
  unfold recentered
  rw [found]

/-- Recentering preserves ambient clearance dominance from the original owner. -/
public theorem recentered_ambientClearanceDominance {parameter : Gaussian}
    (owner : Owner parameter)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner) :
    ExactQuadraticOwnerClearance.AmbientClearanceDominance (recentered owner) := by
  unfold recentered
  generalize resetEq : ExactQuadraticOwnerClearance.movingRecenter? owner = reset
  cases reset with
  | none => exact dominance
  | some moved => exact moved.ownerDominance

end

section
open Purelib.Approximation.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Recentering preserves the original named square root, including the unchanged-owner branch. -/
@[expose] public def recenteredRootEquivalent {parameter : Gaussian} (owner : Owner parameter) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        owner.parameterNonzero owner)
      (SquareRootTrackEquivalence.ownerRootName
        owner.parameterNonzero (recentered owner)) := by
  unfold recentered
  generalize resetEq : ExactQuadraticOwnerClearance.movingRecenter? owner = reset
  cases reset with
  | none => exact Equivalence.NamedEquivalent.refl _
  | some moved => exact movingRecenterRootEquivalent owner moved

/-- Strengthening coefficient clearance preserves the original named square root. -/
@[expose] public def coefficientStrengtheningRootEquivalent {parameter : Gaussian}
    (owner : Owner parameter) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        owner.parameterNonzero owner)
      (SquareRootTrackEquivalence.ownerRootName
        owner.parameterNonzero (QuadraticCoefficientClearance.strengthen owner)) := by
  let common := owner.refineAt 1
  have strict : common.track.initial.box.StrictInterior owner.track.initial.box := by
    change
      (owner.track.refine owner.track.initial
        (Bounds.AccuracyRadius.accuracyRadius
          (CoherentRoot.stepTarget owner.track 0))
        (Bounds.AccuracyRadius.accuracyRadius_pos
          (CoherentRoot.stepTarget_positive owner.track 0))).box.StrictInterior
        owner.track.initial.box
    exact owner.track.strict _ _ _
  have originalToCommon :=
    SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      owner.parameterNonzero owner.track common.track strict
  have strengthenedToCommon :=
    SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      owner.parameterNonzero (QuadraticCoefficientClearance.strengthen owner).track
      common.track (by rw [QuadraticCoefficientClearance.strengthen_box]; exact strict)
  exact Equivalence.NamedEquivalent.trans originalToCommon
    strengthenedToCommon.symm

end

open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Retain an owner with enough clearance, otherwise try coefficient strengthening and then recentering.

The branches preserve the root assignment. The final recentering branch is returned without asserting that it meets the
requested reserve. -/
@[expose] public def retainedAtReserve {parameter : Gaussian} (owner : Owner parameter)
    (reserve : Coordinate) : Owner parameter :=
  if reserve <= owner.track.initial.clearance.bound then owner
  else
    let refreshed := QuadraticCoefficientClearance.strengthen owner
    if reserve ≤ refreshed.track.initial.clearance.bound then refreshed
    else recentered owner

/-- An owner whose original clearance meets the reserve is returned unchanged. -/
public theorem retainedAtReserve_eq_self {parameter : Gaussian}
    (owner : Owner parameter) (reserve : Coordinate)
    (enough : reserve ≤ owner.track.initial.clearance.bound) :
    retainedAtReserve owner reserve = owner := by
  unfold retainedAtReserve
  rw [if_pos enough]

open Purelib.RootIsolation.SquareRoot.Clearance in
/-- When only coefficient strengthening meets the reserve, return that exact strengthened owner. -/
public theorem retainedAtReserve_eq_coefficientStrengthening {parameter : Gaussian}
    (owner : Owner parameter) (reserve : Coordinate)
    (notEnough : ¬ reserve ≤ owner.track.initial.clearance.bound)
    (refreshedEnough : reserve ≤
      (QuadraticCoefficientClearance.strengthen owner).track.initial.clearance.bound) :
    retainedAtReserve owner reserve = QuadraticCoefficientClearance.strengthen owner := by
  unfold retainedAtReserve
  rw [if_neg notEnough]
  exact if_pos refreshedEnough

section
open Purelib.Data.Gaussian
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Zero-reserve transport at an unchanged radicand followed by sufficient reserve retention preserves the original
owner heterogeneously. -/
public theorem retainedReservedTransport_heq_self_of_eq
    {source target : Gaussian} (owner : Owner source)
    (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (reserve : Coordinate)
    (enough : reserve ≤ owner.track.initial.clearance.bound)
    (same : source = target) :
    HEq
      (retainedAtReserve
        (ExactQuadraticOwnerClearance.reservedTransport owner
          targetNonzero small 0) reserve)
      owner := by
  cases same
  rw [ExactQuadraticOwnerClearance.reservedTransport]
  rw [dif_pos rfl]
  rw [retainedAtReserve_eq_self _ _ enough]

/-- Equal source owners produce equal reserved transports followed by reserve retention. -/
public theorem retainedReservedTransport_congr_owner
    {source target : Gaussian} {left right : Owner source}
    (same : left = right)
    (leftTargetNonzero rightTargetNonzero : target ≠ 0)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      left.track.initial.clearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) <
      right.track.initial.clearance.bound)
    (transportReserve retainedReserve : Coordinate) :
    retainedAtReserve
        (ExactQuadraticOwnerClearance.reservedTransport left
          leftTargetNonzero leftSmall transportReserve) retainedReserve =
      retainedAtReserve
        (ExactQuadraticOwnerClearance.reservedTransport right
          rightTargetNonzero rightSmall transportReserve) retainedReserve := by
  subst right
  rfl

end

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Every branch of reserve retention preserves the original named square root. -/
@[expose] public def retainedAtReserveRootEquivalent {parameter : Gaussian}
    (owner : Owner parameter) (reserve : Coordinate) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        owner.parameterNonzero owner)
      (SquareRootTrackEquivalence.ownerRootName
        owner.parameterNonzero (retainedAtReserve owner reserve)) := by
  unfold retainedAtReserve
  by_cases enough : reserve <= owner.track.initial.clearance.bound
  · rw [if_pos enough]
    exact Equivalence.NamedEquivalent.refl _
  · rw [if_neg enough]
    dsimp only
    split
    · exact coefficientStrengtheningRootEquivalent owner
    · exact recenteredRootEquivalent owner

set_option genInjectivity false in
/-- A target segment endpoint and a positive upper bound for the prepared root box's squared diameter.

The target retains its original unit-interval evidence; the positive diameter is the quantitative preparation request.
-/
public structure StepRequest where
  /-- The exact target endpoint with its retained unit-interval evidence. -/ endpoint : Endpoint
  /-- The requested upper bound on the prepared box's squared diagonal. -/ rootDiameter : Coordinate
  /-- Strict positivity of the requested squared-diameter bound. -/ rootDiameterPositive : 0 < rootDiameter

constructive_injectivity StepRequest

open Purelib.Polynomial in
/-- The zero clearance reserve supplied to the exact transport operation for each prepared step. -/
@[expose] public def transportReserve {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (_left : Endpoint) (_request : StepRequest) : Coordinate :=
  0

/-- Interpolate between the current and requested segment parameters, retaining exact endpoint branches at zero and one.
-/
@[expose] public def parameterAt (left : Endpoint) (request : StepRequest)
    (fraction : Coordinate) : Coordinate :=
  if fraction = 0 then left.parameter
  else if fraction = 1 then request.endpoint.parameter
  else left.parameter + fraction *
    (request.endpoint.parameter - left.parameter)

/-- The endpoint-preserving interpolation equals the usual affine parameter formula. -/
public theorem parameterAt_eq_affine (left : Endpoint) (request : StepRequest)
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

/-- Fraction zero selects the original current parameter exactly. -/
@[simp]
public theorem parameterAt_zero (left : Endpoint) (request : StepRequest) :
    parameterAt left request 0 = left.parameter := by
  unfold parameterAt
  rw [if_pos rfl]

/-- Fraction one selects the request's target parameter exactly. -/
@[simp]
public theorem parameterAt_one (left : Endpoint) (request : StepRequest) :
    parameterAt left request 1 = request.endpoint.parameter := by
  unfold parameterAt
  rw [if_neg (show (1 : Coordinate) ≠ 0 by decide), if_pos rfl]

/-- Interpolation by a unit-interval fraction lies between the ordered original endpoints. -/
public theorem parameterAt_between (left : Endpoint) (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    left.parameter <= parameterAt left request fraction ∧
      parameterAt left request fraction <= request.endpoint.parameter := by
  rw [parameterAt_eq_affine]
  have edgeNonnegative :
      (0 : Coordinate) <= request.endpoint.parameter - left.parameter :=
    Fraction.Order.Arithmetic.sub_nonneg_direct ordered
  have localMoveNonnegative :
      0 <= fraction * (request.endpoint.parameter - left.parameter) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct localInside.1
      edgeNonnegative
  have remainingNonnegative :
      0 <= (1 - fraction) *
        (request.endpoint.parameter - left.parameter) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sub_nonneg_direct localInside.2)
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

/-- Interpolation between ordered segment endpoints remains inside the unit interval. -/
public theorem parameterAt_inside (left : Endpoint) (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (0 : Coordinate) <= parameterAt left request fraction ∧
      parameterAt left request fraction <= 1 := by
  have between := parameterAt_between left request ordered fraction localInside
  exact ⟨left.inside.1.trans between.1,
    between.2.trans request.endpoint.inside.2⟩

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Evaluating the original segment at an interpolated parameter agrees with the restricted segment's point. -/
public theorem pointAt_parameterAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (request : StepRequest) (fraction : Coordinate) :
    segment.pointAt (parameterAt left request fraction) =
      (segment.restrict within left.parameter request.endpoint.parameter
        left.inside request.endpoint.inside).pointAt fraction := by
  apply Basic.ext <;>
    simp only [parameterAt_eq_affine,
      Geometry.ClearPath.ClearSegment.pointAt,
      Scale.scale_re, Scale.scale_im,
      Basic.add_re,
      Basic.add_im,
      Basic.sub_re,
      Basic.sub_im] <;> ring1

open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- The owner already meets the requested diameter, predicted clearance, and uniform root-ambient containment.

This readiness predicate does not by itself assert that the requested parameter move fits within the owner's clearance.
-/
@[expose] public def AlreadyPrepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) : Prop :=
  owner.track.initial.box.diagonalSq < request.rootDiameter ∧
    UniformSquareRootPreparation.predictedClearance segment
        request.rootDiameter ≤ owner.track.initial.clearance.bound ∧
      owner.track.initial.box.Refines
        (UniformSquareRootPreparation.rootAmbient segment)

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Decide readiness by checking the three retained rational diameter, clearance, and box-refinement conditions. -/
public instance alreadyPreparedDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) : Decidable (AlreadyPrepared segment current owner request) := by
  unfold AlreadyPrepared Box.Refines
  infer_instance

section
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Strengthen the coefficients of the uniformly prepared owner for the exact segment point and positive diameter
request. -/
@[expose] public def uniformPrepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    Owner (polynomial.eval (segment.pointAt current.parameter)) :=
  QuadraticCoefficientClearance.strengthen
    (UniformSquareRootPreparation.prepared segment
      current.parameter current.inside owner request.rootDiameter request.rootDiameterPositive)

/-- Uniform preparation lies inside the segment's fixed root ambient box. -/
private theorem uniformPrepared_within
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    (uniformPrepared segment current owner request).track.initial.box.Refines
      (UniformSquareRootPreparation.rootAmbient segment) := by
  rw [uniformPrepared, QuadraticCoefficientClearance.strengthen_box,
    UniformSquareRootPreparation.prepared_initial_box]
  exact (UniformSquareRootPreparation.restartInput segment
    current.parameter current.inside owner request.rootDiameter
      request.rootDiameterPositive).centeredBox_refines

/-- Uniform preparation meets the clearance predicted from the requested root diameter. -/
private theorem uniformPrepared_clearance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    UniformSquareRootPreparation.predictedClearance segment request.rootDiameter ≤
      (uniformPrepared segment current owner request).track.initial.clearance.bound := by
  rw [← UniformSquareRootPreparation.prepared_clearance_bound segment
    current.parameter current.inside owner request.rootDiameter request.rootDiameterPositive]
  exact QuadraticCoefficientClearance.strengthen_clearance_le _

/-- Uniform preparation has squared box diameter strictly below the positive request. -/
private theorem uniformPrepared_diameter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    (uniformPrepared segment current owner request).track.initial.box.diagonalSq <
      request.rootDiameter := by
  rw [uniformPrepared, QuadraticCoefficientClearance.strengthen_box]
  exact UniformSquareRootPreparation.prepared_diagonal_lt segment
    current.parameter current.inside owner request.rootDiameterPositive

end

open Purelib.Approximation.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Uniform preparation preserves the named square root selected by the original owner. -/
@[expose] public def uniformPreparedRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    NamedEquivalent
      (owner.certificate owner.parameterNonzero).value.name
      ((uniformPrepared segment current owner request).certificate owner.parameterNonzero).value.name := by
  let common := UniformSquareRootPreparation.bridgeTrack segment
    current.parameter current.inside owner request.rootDiameter request.rootDiameterPositive
  have oldToCommon := SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
    owner.parameterNonzero owner.track common
    (UniformSquareRootPreparation.bridgeTrack_initial_strict_owner
      segment current.parameter current.inside owner request.rootDiameterPositive)
  have newToCommon := SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
    owner.parameterNonzero (uniformPrepared segment current owner request).track common (by
      rw [uniformPrepared, QuadraticCoefficientClearance.strengthen_box]
      exact UniformSquareRootPreparation.bridgeTrack_initial_strict_prepared
        segment current.parameter current.inside owner request.rootDiameterPositive)
  exact Equivalence.NamedEquivalent.trans oldToCommon newToCommon.symm

-- The retry driver shares this lazy fallback with its later uniform-window
-- check.  In particular, a rejected Newton proposal must not reconstruct the
-- identical uniform owner again when that baseline does not carry the edge.
-- Default callers retain the same canonical specification definitionally.
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Choose a ready owner or its exact quadratic strengthening, otherwise a checked candidate or the cached uniform
fallback.

The supplied thunk retains the uniform preparation. A ready owner is strengthened only when its inherited clearance
cannot carry the requested move. -/
@[expose] public def baselinePrepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (uniformCache : Thunk (Owner (polynomial.eval (segment.pointAt current.parameter))) :=
      Thunk.mk fun _ => uniformPrepared segment current owner request) :
    Owner (polynomial.eval (segment.pointAt current.parameter)) :=
  if AlreadyPrepared segment current owner request then
    if ClearSheetContinuation.variationBound segment
        current.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound then
      owner
    else
      ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner
  else
    match (CheckedSquareRootPreparation.attempt segment current.parameter owner
        request.rootDiameter).value with
    | some accepted => accepted.value
    | none => uniformCache.get

/-- The fixed allowance of thirty-three recentering retries in canonical preparation. -/
@[expose] public def preparationRetryCount : Nat := 33

/-- Evidence identifying a retry result with one of the four retained candidate owners.

The alternatives distinguish original coefficient strengthening, moved coefficient strengthening, moved baseline
preparation, and a second recentering. -/
public inductive RetryOrigin {parameter : Gaussian}
    (coefficient movedCoefficient baseline second value : Owner parameter) : Type where
  /-- The selected value equals coefficient strengthening of the original owner. -/ | coefficient (equal : value =
    coefficient)
  /-- The selected value equals coefficient strengthening of the moved owner. -/ | movedCoefficient (equal : value =
    movedCoefficient)
  /-- The selected value equals baseline preparation of the moved owner. -/ | movedBaseline (equal : value = baseline)
  /-- The selected value equals the second recentered owner. -/ | secondReset (equal : value = second)

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
set_option genInjectivity false in
/-- A retained retry candidate with its exact origin, readiness, and clearance for the requested move.

The origin refers to the original candidates; readiness and the strict variation bound certify that this same candidate
can be used. -/
public structure CoefficientRetry
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (moved : Owner (polynomial.eval (segment.pointAt current.parameter))) where
  /-- The exact retained retry candidate at the original source radicand. -/ value : Owner (polynomial.eval
    (segment.pointAt current.parameter))
  /-- Evidence identifying this same candidate with one of the retained retry origins. -/ origin : RetryOrigin
    (QuadraticCoefficientClearance.strengthen owner)
    (QuadraticCoefficientClearance.strengthen moved)
    (baselinePrepared segment current moved request) (recentered moved) value
  /-- The retained owner satisfies the requested diameter, clearance floor, and root-ambient conditions. -/ ready :
    AlreadyPrepared segment current value request
  /-- The requested variation is strictly below this candidate's clearance. -/ carries :
    ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter < value.track.initial.clearance.bound

constructive_injectivity CoefficientRetry

section
open Purelib.Polynomial
section
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Try coefficient strengthening of the original ready owner, then of the moved owner when it is ready.

Success retains the exact selected strengthened owner together with readiness and a strict clearance bound for the move.
Failure certifies no global impossibility. -/
@[expose] public def coefficientProposal?
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (moved : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (ready : AlreadyPrepared segment current owner request) :
    Option (CoefficientRetry segment current owner request moved) :=
  let coefficient := QuadraticCoefficientClearance.strengthen owner
  if carries : ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < coefficient.track.initial.clearance.bound then
    some
      { value := coefficient
        origin := .coefficient rfl
        ready := ⟨by rw [QuadraticCoefficientClearance.strengthen_box]; exact ready.1,
          ready.2.1.trans (QuadraticCoefficientClearance.strengthen_clearance_le owner),
          by rw [QuadraticCoefficientClearance.strengthen_box]; exact ready.2.2⟩
        carries := carries }
  else if movedReady : AlreadyPrepared segment current moved request then
    let movedCoefficient := QuadraticCoefficientClearance.strengthen moved
    if movedCarries : ClearSheetContinuation.variationBound segment current.parameter
        request.endpoint.parameter < movedCoefficient.track.initial.clearance.bound then
      some
        { value := movedCoefficient
          origin := .movedCoefficient rfl
          ready := ⟨by rw [QuadraticCoefficientClearance.strengthen_box]; exact movedReady.1,
            movedReady.2.1.trans (QuadraticCoefficientClearance.strengthen_clearance_le moved),
            by rw [QuadraticCoefficientClearance.strengthen_box]; exact movedReady.2.2⟩
          carries := movedCarries }
    else none
  else none

/-- Try the retained moved baseline, second recentering, or coefficient proposals for a ready original owner.

If the moved owner is already ready and carries the move, return no proposal so the retry driver follows that original
moved owner directly. -/
@[expose] public def coefficientRetry?
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (moved : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    Option (CoefficientRetry segment current owner request moved) :=
  if ready : AlreadyPrepared segment current owner request then
    if movedReady : AlreadyPrepared segment current moved request then
      if movedCarries : ClearSheetContinuation.variationBound segment current.parameter
          request.endpoint.parameter < moved.track.initial.clearance.bound then none
      else
        let strengthened := ExactQuadraticOwnerClearance.strengthenQuadraticOwner moved
        if carries : ClearSheetContinuation.variationBound segment current.parameter
            request.endpoint.parameter < strengthened.track.initial.clearance.bound then
          some
            { value := strengthened
              origin := .movedBaseline (by
                unfold baselinePrepared
                rw [if_pos movedReady, if_neg movedCarries])
              ready := ⟨by rw [ExactQuadraticOwnerClearance.strengthenQuadraticOwner_initial_box]; exact movedReady.1,
                movedReady.2.1.trans (ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_le moved),
                by rw [ExactQuadraticOwnerClearance.strengthenQuadraticOwner_initial_box]; exact movedReady.2.2⟩
              carries := carries }
        else
          let second := recentered moved
          if secondCarries : AlreadyPrepared segment current second request ∧
              ClearSheetContinuation.variationBound segment current.parameter
                request.endpoint.parameter < second.track.initial.clearance.bound then
            some { value := second, origin := .secondReset rfl
                   ready := secondCarries.1, carries := secondCarries.2 }
          else coefficientProposal? segment current owner request moved ready
    else coefficientProposal? segment current owner request moved ready
  else none

end

/-- A ready moved owner that carries the move causes the retry selector to defer to the moved-owner recursion. -/
private theorem coefficientRetry_eq_none_of_moved_carries
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (moved : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (ready : AlreadyPrepared segment current moved request)
    (carries : ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < moved.track.initial.clearance.bound) :
    coefficientRetry? segment current owner request moved = none := by
  unfold coefficientRetry?
  split
  · rfl
  · rfl

open Purelib.Riemann.Branches in
/-- Prepare a root owner with a bounded sequence of recentering and coefficient retries.

Each stage shares one thunk for uniform preparation. Successful carrying candidates are retained; exhaustion returns the
uniform fallback, preserving readiness without claiming that every requested move is small enough. -/
@[expose] public def preparedWithRetries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) : Nat ->
      Owner (polynomial.eval (segment.pointAt current.parameter))
  | 0 =>
      let uniformCache := Thunk.mk fun _ => uniformPrepared segment current owner request
      let baseline := baselinePrepared segment current owner request uniformCache
      if ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
            baseline.track.initial.clearance.bound then
        baseline
      else uniformCache.get
  | retries + 1 =>
      let uniformCache := Thunk.mk fun _ => uniformPrepared segment current owner request
      let baseline := baselinePrepared segment current owner request uniformCache
      if ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
            baseline.track.initial.clearance.bound then
        baseline
      else
        if retries + 1 = preparationRetryCount ∧ ¬ AlreadyPrepared segment current owner request then
          let uniform := uniformCache.get
          if ClearSheetContinuation.variationBound segment
              current.parameter request.endpoint.parameter <
                uniform.track.initial.clearance.bound then
            uniform
          else preparedWithRetries segment current (recentered owner) request retries
        else
          let moved := recentered owner
          match coefficientRetry? segment current owner request moved with
          | some coefficient => coefficient.value
          | none => preparedWithRetries segment current moved request retries

/-- Prepare the exact source owner using the fixed thirty-three-retry procedure.

The result preserves its named root and satisfies the diameter, predicted-clearance, and root-ambient conditions.
Transport still requires an explicit strict variation bound. -/
@[irreducible, expose] public def prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    Owner (polynomial.eval (segment.pointAt current.parameter)) :=
  preparedWithRetries segment current owner request preparationRetryCount

section
open Purelib.Riemann.Branches
/-- Preparation returns the original owner when it is ready and already carries the requested move. -/
public theorem prepared_eq_self_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (carries : ClearSheetContinuation.variationBound segment
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
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current owner request).track.initial.clearance.bound := by
    rw [baselineEq]
    exact carries
  rw [if_pos baselineCarries, baselineEq]

/-- An unready source uses the exact accepted checked candidate when that candidate carries the move. -/
public theorem prepared_eq_checked_of_not_ready
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (notReady : ¬ AlreadyPrepared segment current owner request)
    (accepted : CheckedSquareRootPreparation.Result segment current.parameter
      owner request.rootDiameter)
    (found : (CheckedSquareRootPreparation.attempt segment current.parameter
      owner request.rootDiameter).value = some accepted)
    (carries : ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        accepted.value.track.initial.clearance.bound) :
    prepared segment current owner request = accepted.value := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have baselineEq : baselinePrepared segment current owner request = accepted.value := by
    unfold baselinePrepared
    rw [if_neg notReady, found]
  rw [baselineEq, if_pos carries]

end

open Purelib.RootIsolation.SquareRoot.Clearance in
/-- An unready source uses the uniform fallback when the checked candidate cannot carry the move but the fallback can.
-/
public theorem prepared_eq_uniform_of_not_ready_of_checked_miss
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (notReady : ¬ AlreadyPrepared segment current owner request)
    (accepted : CheckedSquareRootPreparation.Result segment current.parameter
      owner request.rootDiameter)
    (found : (CheckedSquareRootPreparation.attempt segment current.parameter
      owner request.rootDiameter).value = some accepted)
    (misses : ¬ ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter < accepted.value.track.initial.clearance.bound)
    (uniformCarries : ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        (QuadraticCoefficientClearance.strengthen
          (UniformSquareRootPreparation.prepared segment current.parameter current.inside owner
            request.rootDiameter request.rootDiameterPositive)).track.initial.clearance.bound) :
    prepared segment current owner request =
      QuadraticCoefficientClearance.strengthen
        (UniformSquareRootPreparation.prepared segment current.parameter current.inside owner
          request.rootDiameter request.rootDiameterPositive) := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have baselineEq : baselinePrepared segment current owner request = accepted.value := by
    unfold baselinePrepared
    rw [if_neg notReady, found]
  have quick : 32 + 1 = preparationRetryCount ∧ ¬ AlreadyPrepared segment current owner request :=
    ⟨rfl, notReady⟩
  have carries : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (uniformPrepared segment current owner request).track.initial.clearance.bound := uniformCarries
  rw [baselineEq, if_neg misses, if_pos quick]
  simp only [Thunk.get]
  rw [if_pos carries]
  rfl

section
open Purelib.Riemann.Branches
open Purelib.RootIsolation.SquareRoot.Clearance
/-- A ready source whose inherited clearance fails uses its exact quadratic strengthening when that strengthening
carries the move. -/
public theorem prepared_eq_strengthenQuadraticOwner_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (notCarries : ¬ ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound)
    (strengthenedCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound) :
    prepared segment current owner request = ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have baselineEq :
      baselinePrepared segment current owner request =
        ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner := by
    unfold baselinePrepared
    rw [if_pos ready, if_neg notCarries]
  have baselineCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current owner request).track.initial.clearance.bound := by
    rw [baselineEq]
    exact strengthenedCarries
  rw [if_pos baselineCarries, baselineEq]

/-- Preparation of a ready owner carries the move whenever its exact quadratic strengthening does. -/
public theorem variation_lt_prepared_of_ready_of_strengthenedCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (strengthenedCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound) :
    ClearSheetContinuation.variationBound segment
        current.parameter request.endpoint.parameter <
      (prepared segment current owner request).track.initial.clearance.bound := by
  by_cases carries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact carries
  · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
      request ready carries strengthenedCarries]
    exact strengthenedCarries

/-- Preparation keeps the original initial box when readiness and a carrying quadratic strengthening suffice. -/
public theorem prepared_initial_box_eq_of_ready_of_strengthenedCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (strengthenedCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound) :
    (prepared segment current owner request).track.initial.box =
      owner.track.initial.box := by
  by_cases carries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
  · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
      request ready carries strengthenedCarries,
      ExactQuadraticOwnerClearance.strengthenQuadraticOwner_initial_box]

/-- Preparation preserves ambient clearance dominance when a ready owner's quadratic strengthening carries the move. -/
public theorem prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (strengthenedCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner) :
    ExactQuadraticOwnerClearance.AmbientClearanceDominance (prepared segment current owner request) := by
  by_cases carries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact dominance
  · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
      request ready carries strengthenedCarries]
    exact ExactQuadraticOwnerClearance.strengthenQuadraticOwner_ambientClearanceDominance_of owner dominance

/-- Preparation preserves the quadratic ambient budget when a ready owner's quadratic strengthening carries the move. -/
public theorem prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (strengthenedCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner) :
    ExactQuadraticOwnerClearance.QuadraticAmbientBudget (prepared segment current owner request) := by
  by_cases carries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact budget
  · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
      request ready carries strengthenedCarries]
    exact ExactQuadraticOwnerClearance.strengthenQuadraticOwner_quadraticAmbientBudget owner budget

/-- A lower bound for variation minus displacement also bounds the prepared clearance margin when quadratic
strengthening carries the move. -/
public theorem prepared_margin_lower_of_ready_of_strengthenedCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (strengthenedCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound)
    (floor displacement : Coordinate)
    (variationMargin : floor ≤
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter - displacement) :
    floor ≤ (prepared segment current owner request).track.initial.clearance.bound -
      displacement := by
  by_cases carries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact variationMargin.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct carries.le
        displacement)
  · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
      request ready carries strengthenedCarries]
    exact variationMargin.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct
        strengthenedCarries.le displacement)

/-- Preparation selects the exact first recentered owner after inherited and strengthened clearance fail, provided that
recentered owner is ready and carries the move. -/
public theorem prepared_eq_recentered_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (notCarries : ¬ ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound)
    (strengthenedNotCarries :
      ¬ ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound)
    (recenteredReady : AlreadyPrepared segment current (recentered owner)
      request)
    (recenteredCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound) :
    prepared segment current owner request = recentered owner := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have firstBaselineEq :
      baselinePrepared segment current owner request =
        ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner := by
    unfold baselinePrepared
    rw [if_pos ready, if_neg notCarries]
  have firstBaselineNotCarries :
      ¬ ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current owner request).track.initial.clearance.bound := by
    rw [firstBaselineEq]
    exact strengthenedNotCarries
  rw [if_neg firstBaselineNotCarries]
  rw [if_neg (fun failed : 33 = preparationRetryCount ∧
    ¬ AlreadyPrepared segment current owner request => failed.2 ready)]
  dsimp only
  have secondBaselineEq :
      baselinePrepared segment current (recentered owner) request =
        recentered owner := by
    unfold baselinePrepared
    rw [if_pos recenteredReady, if_pos recenteredCarries]
  have secondBaselineCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current (recentered owner)
          request).track.initial.clearance.bound := by
    rw [secondBaselineEq]
    exact recenteredCarries
  rw [show 32 = 31 + 1 by rfl, preparedWithRetries,
    if_pos secondBaselineCarries, secondBaselineEq]
  rw [coefficientRetry_eq_none_of_moved_carries segment current owner request
    (recentered owner) recenteredReady recenteredCarries]

/-- Preparation selects the exact second recentered owner when the earlier ready candidates fail and the second one is
ready and carries the move. -/
public theorem prepared_eq_recentered_twice_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (notCarries : ¬ ClearSheetContinuation.variationBound segment
      current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound)
    (strengthenedNotCarries :
      ¬ ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound)
    (firstReady : AlreadyPrepared segment current (recentered owner) request)
    (firstNotCarries :
      ¬ ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound)
    (firstStrengthenedNotCarries :
      ¬ ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner (recentered owner)).track.initial.clearance.bound)
    (secondReady : AlreadyPrepared segment current
      (recentered (recentered owner)) request)
    (secondCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered (recentered owner)).track.initial.clearance.bound) :
    prepared segment current owner request =
      recentered (recentered owner) := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have firstBaselineEq :
      baselinePrepared segment current owner request =
        ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner := by
    unfold baselinePrepared
    rw [if_pos ready, if_neg notCarries]
  have firstBaselineNotCarries :
      ¬ ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (baselinePrepared segment current owner request).track.initial.clearance.bound := by
    rw [firstBaselineEq]
    exact strengthenedNotCarries
  rw [if_neg firstBaselineNotCarries]
  rw [if_neg (fun failed : 33 = preparationRetryCount ∧
    ¬ AlreadyPrepared segment current owner request => failed.2 ready)]
  dsimp only
  unfold coefficientRetry?
  rw [dif_pos ready, dif_pos firstReady, dif_neg firstNotCarries,
    dif_neg firstStrengthenedNotCarries, dif_pos ⟨secondReady, secondCarries⟩]

end

section
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Preparation selects the exact quadratic strengthening of the first recentered owner when the earlier carrying tests
fail. -/
public theorem prepared_eq_strengthened_recentered_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (inheritedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < owner.track.initial.clearance.bound)
    (directMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < (ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound)
    (movedReady : AlreadyPrepared segment current (recentered owner) request)
    (movedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < (recentered owner).track.initial.clearance.bound)
    (carries : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (ExactQuadraticOwnerClearance.strengthenQuadraticOwner (recentered owner)).track.initial.clearance.bound) :
    prepared segment current owner request = ExactQuadraticOwnerClearance.strengthenQuadraticOwner (recentered owner) :=
      by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have baselineEq : baselinePrepared segment current owner request =
    ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner := by
    unfold baselinePrepared
    rw [if_pos ready, if_neg inheritedMiss]
  rw [baselineEq, if_neg directMiss]
  rw [if_neg (fun failed : 33 = preparationRetryCount ∧
    ¬ AlreadyPrepared segment current owner request => failed.2 ready)]
  dsimp only
  unfold coefficientRetry?
  rw [dif_pos ready, dif_pos movedReady, dif_neg movedMiss, dif_pos carries]

/-- Preparation selects the original owner's coefficient strengthening when earlier moved candidates fail and this
proposal carries the move. -/
public theorem prepared_eq_coefficient_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (inheritedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < owner.track.initial.clearance.bound)
    (directMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < (ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound)
    (movingMiss : ¬ (AlreadyPrepared segment current (recentered owner) request ∧
      ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound))
    (movedStrengthenedMiss : AlreadyPrepared segment current (recentered owner) request →
      ¬ ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner (recentered owner)).track.initial.clearance.bound)
    (secondMiss : AlreadyPrepared segment current (recentered owner) request →
      ¬ (AlreadyPrepared segment current (recentered (recentered owner)) request ∧
        ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
          (recentered (recentered owner)).track.initial.clearance.bound))
    (carries : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (QuadraticCoefficientClearance.strengthen owner).track.initial.clearance.bound) :
    prepared segment current owner request = QuadraticCoefficientClearance.strengthen owner := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have baselineEq : baselinePrepared segment current owner request =
    ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner := by
    unfold baselinePrepared
    rw [if_pos ready, if_neg inheritedMiss]
  rw [baselineEq, if_neg directMiss]
  rw [if_neg (fun failed : 33 = preparationRetryCount ∧
    ¬ AlreadyPrepared segment current owner request => failed.2 ready)]
  dsimp only
  unfold coefficientRetry?
  rw [dif_pos ready]
  by_cases movedReady : AlreadyPrepared segment current (recentered owner) request
  · rw [dif_pos movedReady, dif_neg (fun carrying => movingMiss ⟨movedReady, carrying⟩),
      dif_neg (movedStrengthenedMiss movedReady), dif_neg (secondMiss movedReady)]
    rw [coefficientProposal?, dif_pos carries]
  · rw [dif_neg movedReady, coefficientProposal?, dif_pos carries]

/-- Preparation selects coefficient strengthening of the moved owner when all earlier candidates fail and this proposal
carries the move. -/
public theorem prepared_eq_moved_coefficient_of_ready
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (inheritedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < owner.track.initial.clearance.bound)
    (directMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < (ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound)
    (movedReady : AlreadyPrepared segment current (recentered owner) request)
    (movingMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < (recentered owner).track.initial.clearance.bound)
    (movedStrengthenedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < (ExactQuadraticOwnerClearance.strengthenQuadraticOwner (recentered
        owner)).track.initial.clearance.bound)
    (secondMiss : ¬ (AlreadyPrepared segment current (recentered (recentered owner)) request ∧
      ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
        (recentered (recentered owner)).track.initial.clearance.bound))
    (coefficientMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < (QuadraticCoefficientClearance.strengthen owner).track.initial.clearance.bound)
    (carries : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (QuadraticCoefficientClearance.strengthen (recentered owner)).track.initial.clearance.bound) :
    prepared segment current owner request =
      QuadraticCoefficientClearance.strengthen (recentered owner) := by
  unfold prepared
  rw [show preparationRetryCount = 33 by rfl, preparedWithRetries]
  have baselineEq : baselinePrepared segment current owner request =
    ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner := by
    unfold baselinePrepared
    rw [if_pos ready, if_neg inheritedMiss]
  rw [baselineEq, if_neg directMiss]
  rw [if_neg (fun failed : 33 = preparationRetryCount ∧
    ¬ AlreadyPrepared segment current owner request => failed.2 ready)]
  dsimp only
  unfold coefficientRetry?
  rw [dif_pos ready, dif_pos movedReady, dif_neg movingMiss,
    dif_neg movedStrengthenedMiss, dif_neg secondMiss]
  rw [coefficientProposal?, dif_neg coefficientMiss, dif_pos movedReady, dif_pos carries]

end

open Purelib.Riemann.Branches
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Preparation carries the move when both the original and recentered owner are ready and the recentered owner carries
it. -/
public theorem variation_lt_prepared_of_ready_of_recenteredCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (recenteredReady : AlreadyPrepared segment current (recentered owner)
      request)
    (recenteredCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound) :
    ClearSheetContinuation.variationBound segment
        current.parameter request.endpoint.parameter <
      (prepared segment current owner request).track.initial.clearance.bound := by
  by_cases carries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact carries
  · by_cases strengthenedCarries :
        ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
        request ready carries strengthenedCarries]
      exact strengthenedCarries
    · rw [prepared_eq_recentered_of_ready segment current owner request ready
        carries strengthenedCarries recenteredReady recenteredCarries]
      exact recenteredCarries

/-- Preparation preserves ambient dominance when a ready recentered owner supplies the carrying fallback. -/
public theorem prepared_ambientClearanceDominance_of_ready_of_recenteredCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (recenteredReady : AlreadyPrepared segment current (recentered owner)
      request)
    (recenteredCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner) :
    ExactQuadraticOwnerClearance.AmbientClearanceDominance (prepared segment current owner request) := by
  by_cases carries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact dominance
  · by_cases strengthenedCarries :
        ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
        request ready carries strengthenedCarries]
      exact ExactQuadraticOwnerClearance.strengthenQuadraticOwner_ambientClearanceDominance_of owner dominance
    · rw [prepared_eq_recentered_of_ready segment current owner request ready
        carries strengthenedCarries recenteredReady recenteredCarries]
      exact recentered_ambientClearanceDominance owner dominance

/-- Preparation retains a quadratic ambient budget when both the original and carrying recentered candidate have one. -/
public theorem prepared_quadraticAmbientBudget_of_ready_of_recenteredCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (recenteredReady : AlreadyPrepared segment current (recentered owner)
      request)
    (recenteredCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner)
    (recenteredBudget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget (recentered owner)) :
    ExactQuadraticOwnerClearance.QuadraticAmbientBudget (prepared segment current owner request) := by
  by_cases carries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact budget
  · by_cases strengthenedCarries :
        ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
        request ready carries strengthenedCarries]
      exact ExactQuadraticOwnerClearance.strengthenQuadraticOwner_quadraticAmbientBudget owner budget
    · rw [prepared_eq_recentered_of_ready segment current owner request ready
        carries strengthenedCarries recenteredReady recenteredCarries]
      exact recenteredBudget

/-- Preparation retains a clearance-minus-displacement floor supplied for both the variation and the carrying recentered
owner. -/
public theorem prepared_margin_lower_of_ready_of_recenteredCarries
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (recenteredReady : AlreadyPrepared segment current (recentered owner)
      request)
    (recenteredCarries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        (recentered owner).track.initial.clearance.bound)
    (floor displacement : Coordinate)
    (variationMargin : floor ≤
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter - displacement)
    (recenteredMargin : floor ≤
      (recentered owner).track.initial.clearance.bound - displacement) :
    floor ≤ (prepared segment current owner request).track.initial.clearance.bound -
      displacement := by
  by_cases carries :
      ClearSheetContinuation.variationBound segment
          current.parameter request.endpoint.parameter <
        owner.track.initial.clearance.bound
  · rw [prepared_eq_self_of_ready segment current owner request ready carries]
    exact variationMargin.trans
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct carries.le
        displacement)
  · by_cases strengthenedCarries :
        ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment current owner
        request ready carries strengthenedCarries]
      exact variationMargin.trans
        (Fraction.Order.Arithmetic.sub_le_sub_right_direct
          strengthenedCarries.le displacement)
    · rw [prepared_eq_recentered_of_ready segment current owner request ready
        carries strengthenedCarries recenteredReady recenteredCarries]
      exact recenteredMargin

end

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A retained prepared owner with equality to the canonical preparation of the exact source and request.

Subsequent transport can consume this owner directly; the equality connects its cached data to the public preparation
operation. -/
public structure CachedSource {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) where
  /-- The exact prepared owner retained for reuse by later transport. -/ preparedOwner : Owner
    (polynomial.eval (segment.pointAt current.parameter))
  /-- Equality of the cached owner with canonical preparation of the original inputs. -/ preparedOwner_eq :
    preparedOwner = prepared segment current owner request

constructive_injectivity CachedSource

namespace CachedSource

open Purelib.Polynomial
/-- Cache the exact canonical prepared owner for the original segment point, owner, and request. -/
@[expose] public def canonical {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) : CachedSource segment current owner request where
  preparedOwner := prepared segment current owner request
  preparedOwner_eq := rfl

/-- Every certified cache equals the canonical cache for the same original preparation inputs. -/
public theorem eq_canonical {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
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

section
open Purelib.Polynomial
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Every baseline preparation lies in the segment's fixed root ambient box. -/
private theorem baselinePrepared_initial_box_refines_rootAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    (baselinePrepared segment current owner request).track.initial.box.Refines
      (UniformSquareRootPreparation.rootAmbient segment) := by
  unfold baselinePrepared
  by_cases ready : AlreadyPrepared segment current owner request
  · rw [if_pos ready]
    by_cases carries :
        ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound
    · rw [if_pos carries]
      exact ready.2.2
    · rw [if_neg carries, ExactQuadraticOwnerClearance.strengthenQuadraticOwner_initial_box]
      exact ready.2.2
  · rw [if_neg ready]
    cases found : (CheckedSquareRootPreparation.attempt segment current.parameter
        owner request.rootDiameter).value with
    | some accepted => exact accepted.within
    | none => exact uniformPrepared_within segment current owner request

open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Every branch of bounded preparation lies in the segment's fixed root ambient box. -/
public theorem prepared_initial_box_refines_rootAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    (prepared segment current owner request).track.initial.box.Refines
      (UniformSquareRootPreparation.rootAmbient segment) := by
  unfold prepared
  have retryRefines : forall (retries : Nat)
      (candidate : Owner
        (polynomial.eval (segment.pointAt current.parameter))),
      (preparedWithRetries segment current candidate request retries).track.initial.box.Refines
        (UniformSquareRootPreparation.rootAmbient segment) := by
    intro retries
    induction retries with
    | zero =>
        intro candidate
        simp only [preparedWithRetries, Thunk.get]
        by_cases carries : ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
              (baselinePrepared segment current candidate request).track.initial.clearance.bound
        · rw [if_pos carries]
          exact baselinePrepared_initial_box_refines_rootAmbient segment current candidate request
        · rw [if_neg carries]
          exact uniformPrepared_within segment current candidate request
    | succ retries inductionHypothesis =>
        intro candidate
        simp only [preparedWithRetries, Thunk.get]
        by_cases carries :
            ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
              (baselinePrepared segment current candidate
                request).track.initial.clearance.bound
        · rw [if_pos carries]
          exact baselinePrepared_initial_box_refines_rootAmbient segment current
            candidate request
        · rw [if_neg carries]
          by_cases quick : retries + 1 = preparationRetryCount ∧
              ¬ AlreadyPrepared segment current candidate request
          · rw [if_pos quick]
            by_cases uniformCarries : ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
                  (uniformPrepared segment current candidate request).track.initial.clearance.bound
            · rw [if_pos uniformCarries]
              exact uniformPrepared_within segment current candidate request
            · rw [if_neg uniformCarries]
              exact inductionHypothesis (recentered candidate)
          · rw [if_neg quick]
            cases coefficientRetry? segment current candidate request (recentered candidate) with
            | none => exact inductionHypothesis (recentered candidate)
            | some coefficient => exact coefficient.ready.2.2
  exact retryRefines preparationRetryCount owner

section
open Purelib.Riemann.RootContinuation
/-- The uniform predicted clearance determined by the segment and requested positive root diameter. -/
@[expose] public def preparedClearanceLower
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (_current : Endpoint) (request : StepRequest) : Coordinate :=
  UniformSquareRootPreparation.predictedClearance segment
    request.rootDiameter

/-- The predicted clearance for a positive root-diameter request is strictly positive. -/
public theorem preparedClearanceLower_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) :
    0 < preparedClearanceLower segment current request :=
  UniformSquareRootPreparation.predictedClearance_positive segment
    request.rootDiameter request.rootDiameterPositive

/-- The minimum of the predicted clearance and one for a segment and root diameter. -/
@[expose] public def uniformPreparedClearanceFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) : Coordinate :=
  min
    (UniformSquareRootPreparation.predictedClearance segment
      rootDiameter)
    1

/-- The capped uniform clearance floor is positive for a positive diameter. -/
public theorem uniformPreparedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < uniformPreparedClearanceFloor segment rootDiameter :=
  Fraction.Order.Basic.lt_min
    (UniformSquareRootPreparation.predictedClearance_positive
      segment rootDiameter rootDiameterPositive)
    (by decide)

/-- The capped uniform clearance floor does not exceed the predicted clearance. -/
public theorem uniformPreparedClearanceFloor_le_predicted
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) :
    uniformPreparedClearanceFloor segment rootDiameter <=
      UniformSquareRootPreparation.predictedClearance segment
        rootDiameter :=
  Fraction.Order.Basic.min_le_left _ _

end

open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Every prepared owner meets the request's predicted clearance lower bound. -/
public theorem preparedClearanceLower_le
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
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
          ClearSheetContinuation.variationBound segment
              current.parameter request.endpoint.parameter <
            candidate.track.initial.clearance.bound
      · rw [if_pos carries]
        exact ready.2.1
      · rw [if_neg carries]
        exact ready.2.1.trans (ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_le candidate)
    · rw [if_neg ready]
      cases found : (CheckedSquareRootPreparation.attempt segment current.parameter
          candidate request.rootDiameter).value with
      | some accepted => exact accepted.clearance
      | none => exact uniformPrepared_clearance segment current candidate request
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
        simp only [preparedWithRetries, Thunk.get]
        by_cases carries : ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
              (baselinePrepared segment current candidate request).track.initial.clearance.bound
        · rw [if_pos carries]
          exact baselineLower candidate
        · rw [if_neg carries]
          exact uniformPrepared_clearance segment current candidate request
    | succ retries inductionHypothesis =>
        intro candidate
        simp only [preparedWithRetries, Thunk.get]
        by_cases carries :
            ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
              (baselinePrepared segment current candidate
                request).track.initial.clearance.bound
        · rw [if_pos carries]
          exact baselineLower candidate
        · rw [if_neg carries]
          by_cases quick : retries + 1 = preparationRetryCount ∧
              ¬ AlreadyPrepared segment current candidate request
          · rw [if_pos quick]
            by_cases uniformCarries : ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
                  (uniformPrepared segment current candidate request).track.initial.clearance.bound
            · rw [if_pos uniformCarries]
              exact uniformPrepared_clearance segment current candidate request
            · rw [if_neg uniformCarries]
              exact inductionHypothesis (recentered candidate)
          · rw [if_neg quick]
            cases coefficientRetry? segment current candidate request (recentered candidate) with
            | none => exact inductionHypothesis (recentered candidate)
            | some coefficient => exact coefficient.ready.2.1
  exact retryLower preparationRetryCount owner

/-- Read the coherent square-root name of the exact prepared source owner. -/
@[expose] public def preparedRootName {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) : Named :=
  ((prepared segment left owner request).certificate
    (segment.pointAt_eval_ne_zero left.parameter left.inside)).value.name

end

open Purelib.Data.Gaussian in
/-- Zero squared displacement is strictly smaller than an owner's positive clearance. -/
public theorem samePointSmall {parameter : Gaussian} (owner : Owner parameter) :
    Data.Gaussian.Norm.Basic.normSq (parameter - parameter) <
      owner.track.initial.clearance.bound := by
  rw [Basic.sub_self,
    Norm.Basic.normSq_zero]
  exact owner.track.initial.clearance.positive

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Read the root name after zero-reserve transport of the prepared owner to its unchanged radicand. -/
@[expose] public def zeroMoveRootName {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) : Named :=
  let source := prepared segment left owner request
  let nonzero := segment.pointAt_eval_ne_zero left.parameter left.inside
  ((ExactQuadraticOwnerClearance.reservedTransport source nonzero (samePointSmall source)
    (transportReserve segment left request)).certificate nonzero).value.name

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Every prepared initial box has squared diagonal strictly smaller than the requested root diameter. -/
public theorem prepared_diagonal_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
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
          ClearSheetContinuation.variationBound segment
              current.parameter request.endpoint.parameter <
            candidate.track.initial.clearance.bound
      · rw [if_pos carries]
        exact ready.1
      · rw [if_neg carries, ExactQuadraticOwnerClearance.strengthenQuadraticOwner_initial_box]
        exact ready.1
    · rw [if_neg ready]
      cases found : (CheckedSquareRootPreparation.attempt segment current.parameter
          candidate request.rootDiameter).value with
      | some accepted => exact accepted.diameter
      | none => exact uniformPrepared_diameter segment current candidate request
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
        simp only [preparedWithRetries, Thunk.get]
        by_cases carries : ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
              (baselinePrepared segment current candidate request).track.initial.clearance.bound
        · rw [if_pos carries]
          exact baselineSmall candidate
        · rw [if_neg carries]
          exact uniformPrepared_diameter segment current candidate request
    | succ retries inductionHypothesis =>
        intro candidate
        simp only [preparedWithRetries, Thunk.get]
        by_cases carries :
            ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
              (baselinePrepared segment current candidate
                request).track.initial.clearance.bound
        · rw [if_pos carries]
          exact baselineSmall candidate
        · rw [if_neg carries]
          by_cases quick : retries + 1 = preparationRetryCount ∧
              ¬ AlreadyPrepared segment current candidate request
          · rw [if_pos quick]
            by_cases uniformCarries : ClearSheetContinuation.variationBound segment
                current.parameter request.endpoint.parameter <
                  (uniformPrepared segment current candidate request).track.initial.clearance.bound
            · rw [if_pos uniformCarries]
              exact uniformPrepared_diameter segment current candidate request
            · rw [if_neg uniformCarries]
              exact inductionHypothesis (recentered candidate)
          · rw [if_neg quick]
            cases coefficientRetry? segment current candidate request (recentered candidate) with
            | none => exact inductionHypothesis (recentered candidate)
            | some coefficient => exact coefficient.ready.1
  exact retrySmall preparationRetryCount owner

/-- Transport the exact prepared source owner to the requested endpoint using the retained variation bound.

The segment's ambient containment turns the strict variation estimate into the squared-displacement certificate required
by zero-reserve transport. -/
@[expose] public def transported {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    Owner (polynomial.eval
      (segment.pointAt request.endpoint.parameter)) :=
  ExactQuadraticOwnerClearance.reservedTransport (prepared segment left owner request)
    (segment.pointAt_eval_ne_zero request.endpoint.parameter
      request.endpoint.inside)
    ((ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt small)
    (transportReserve segment left request)

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Read the coherent square-root name of the exact transported owner at the requested endpoint. -/
@[expose] public def transportedRootName {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) : Named :=
  ((transported segment within left owner request small).certificate
    (segment.pointAt_eval_ne_zero request.endpoint.parameter
      request.endpoint.inside)).value.name

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- A retained direct-presentation relation identifies the result's root with generic advancement of the same source.

The comparison uses the relation's original parent and strict refinements, then a common tail of the actual result
owner. -/
@[expose] public def rootEquivalentOfDirectPresentation
    {source target : Gaussian} (sourceOwner : Owner source)
    (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceOwner.track.initial.clearance.bound)
    (result : Owner target)
    (relation : ExactQuadraticOwnerClearance.DirectPresentationRelation sourceOwner targetNonzero small
      result) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName targetNonzero
        (sourceOwner.advance targetNonzero small))
      (SquareRootTrackEquivalence.ownerRootName targetNonzero
        result) := by
  let tail := result.refineAt 1
  have tailStrictResult : tail.track.initial.box.StrictInterior
      result.track.initial.box := by
    change (CoherentRoot.state result.track 1).box.StrictInterior
      result.track.initial.box
    exact SquareRootTrackEquivalence.state_strict_initial_of_pos
      result.track (by decide)
  have tailStrictParent : tail.track.initial.box.StrictInterior
      relation.parent.track.initial.box :=
    (Geometry.Rational.Box.Refinement.StrictInterior.Boxes.trans_refines tailStrictResult) relation.resultRefinesParent
  have genericToParent :=
    (SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      targetNonzero relation.parent.track
        (sourceOwner.advance targetNonzero small).track
        relation.genericStrictParent).symm
  have parentToTail :=
    SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      targetNonzero relation.parent.track tail.track tailStrictParent
  have resultToTail :=
    SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      targetNonzero result.track tail.track tailStrictResult
  exact Equivalence.NamedEquivalent.trans genericToParent
    (Equivalence.NamedEquivalent.trans parentToTail
      resultToTail.symm)

section
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Direct transport and generic advancement of the same source name equivalent roots at the exact target. -/
@[expose] public def directTransportRootEquivalentGeneric
    {source target : Gaussian} (sourceOwner : Owner source)
    (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceOwner.track.initial.clearance.bound) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName targetNonzero
        (sourceOwner.advance targetNonzero small))
      (SquareRootTrackEquivalence.ownerRootName targetNonzero
        (ExactQuadraticOwnerClearance.directTransport sourceOwner targetNonzero small)) := by
  rcases directTransport_generic_relation sourceOwner targetNonzero small with
      equal | strict
  · rw [equal]
    exact Equivalence.NamedEquivalent.refl _
  · exact rootEquivalentOfDirectPresentation sourceOwner targetNonzero small
      (ExactQuadraticOwnerClearance.directTransport sourceOwner targetNonzero small) strict

/-- Reserved transport and generic advancement of the same source name equivalent roots at the exact target. -/
@[expose] public def reservedTransportRootEquivalentGeneric
    {source target : Gaussian} (sourceOwner : Owner source)
    (targetNonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) <
      sourceOwner.track.initial.clearance.bound)
    (reserve : Coordinate) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName targetNonzero
        (sourceOwner.advance targetNonzero small))
      (SquareRootTrackEquivalence.ownerRootName targetNonzero
        (ExactQuadraticOwnerClearance.reservedTransport sourceOwner targetNonzero small reserve)) := by
  rcases reservedTransport_generic_relation sourceOwner targetNonzero small
      reserve with equal | strict
  · rw [equal]
    exact Equivalence.NamedEquivalent.refl _
  · exact rootEquivalentOfDirectPresentation sourceOwner targetNonzero small
      (ExactQuadraticOwnerClearance.reservedTransport sourceOwner targetNonzero small reserve) strict

end

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- The reserved-transport root name is independent of the supplied proofs of target nonzeroness and small displacement.
-/
public theorem reservedTransportRootName_proof_irrel
    {source target : Gaussian} (sourceOwner : Owner source)
    (firstNonzero secondNonzero : target ≠ 0)
    (firstSmall secondSmall :
      Data.Gaussian.Norm.Basic.normSq (source - target) <
        sourceOwner.track.initial.clearance.bound)
    (reserve : Coordinate) :
    SquareRootTrackEquivalence.ownerRootName firstNonzero
        (ExactQuadraticOwnerClearance.reservedTransport sourceOwner firstNonzero firstSmall reserve) =
      SquareRootTrackEquivalence.ownerRootName secondNonzero
        (ExactQuadraticOwnerClearance.reservedTransport sourceOwner secondNonzero secondSmall reserve) := by
  have nonzero_eq : firstNonzero = secondNonzero :=
    Subsingleton.elim _ _
  cases nonzero_eq
  have small_eq : firstSmall = secondSmall := Subsingleton.elim _ _
  cases small_eq
  rfl

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Generic continuation of the prepared source and its reserved transport yield equivalent root names. -/
@[expose] public def continuedRootNameEquivalentTransportedRootName
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    NamedEquivalent
      (SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        (prepared segment left owner request)
        (by simpa only [Norm.Basic.normSq_eq_canonical] using ((ClearSheetContinuation.evaluation_variation_le segment
          within left.parameter request.endpoint.parameter left.inside
            request.endpoint.inside).trans_lt small)))
      (transportedRootName segment within left owner request small) := by
  let source := prepared segment left owner request
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let normSmall :=
    (ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt small
  exact reservedTransportRootEquivalentGeneric source targetNonzero normSmall
    (transportReserve segment left request)

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- The transported anchor's squared displacement from the prepared anchor is below the requested diameter. -/
public theorem transported_anchor_distance_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    Data.Gaussian.Norm.Basic.normSq
        ((transported segment within left owner request small).track.initial.box.anchor -
          (prepared segment left owner request).track.initial.box.anchor) <
      request.rootDiameter := by
  let source := prepared segment left owner request
  let target := transported segment within left owner request small
  have refines : target.track.initial.box.Refines
      source.track.initial.box := by
    exact ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines source
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside) _
      (transportReserve segment left request)
  exact (source.track.initial.box.normSq_sub_le_diagonalSq
    (refines.contains target.track.initial.box.contains_anchor)
    source.track.initial.box.contains_anchor).trans_lt
      (prepared_diagonal_lt segment left owner request)

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Transport the prepared owner to an interpolated point of the ordered requested parameter interval.

The full step's strict variation bound bounds every intermediate move; the same prepared source and transport reserve
are retained. -/
@[expose] public def transportedInterior {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Owner (polynomial.eval
      (segment.pointAt (parameterAt left request fraction))) := by
  let parameter := parameterAt left request fraction
  have between := parameterAt_between left request ordered fraction localInside
  have localSmall :
      ClearSheetContinuation.variationBound segment
          left.parameter parameter <
        (prepared segment left owner request).track.initial.clearance.bound :=
    (ClearSheetContinuation.variationBound_le_of_between
      segment between.1 between.2).trans_lt small
  exact ExactQuadraticOwnerClearance.reservedTransport (prepared segment left owner request)
    (segment.pointAt_eval_ne_zero parameter
      (parameterAt_inside left request ordered fraction localInside))
    ((ClearSheetContinuation.evaluation_variation_le segment within
      left.parameter parameter left.inside
        (parameterAt_inside left request ordered fraction localInside)).trans_lt
          localSmall)
    (transportReserve segment left request)

/-- Transport to an intermediate point refines the exact prepared source box. -/
public theorem transportedInterior_initial_box_refines
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (transportedInterior segment within left owner request ordered small
      fraction localInside).track.initial.box.Refines
        (prepared segment left owner request).track.initial.box := by
  let parameter := parameterAt left request fraction
  exact ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines
    (prepared segment left owner request)
    (segment.pointAt_eval_ne_zero parameter
      (parameterAt_inside left request ordered fraction localInside)) _
    (transportReserve segment left request)

end

set_option genInjectivity false in
/-- A target root owner with refinement of its initial box into the retained source box.

The radicand and source box are indices of the certificate, so readback and containment concern those exact inputs. -/
public structure TransportedQuery (parameter : Gaussian) (source : Box) where
  /-- The exact transported owner at the query's indexed radicand. -/ owner : Owner parameter
  /-- The query owner's initial box refines the indexed source box. -/ initial_box_refines :
    owner.track.initial.box.Refines source

constructive_injectivity TransportedQuery

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Construct a transported query at any unit-interval fraction, retaining specialized endpoint computations.

Fraction zero uses the exact zero-move transport, fraction one uses the endpoint transport, and other fractions use
interior transport. Every result retains refinement into the same prepared source box. -/
@[expose] public def transportedQuery {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
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
    let queryOwner := ExactQuadraticOwnerClearance.reservedTransport (prepared segment left owner request)
      (segment.pointAt_eval_ne_zero left.parameter left.inside)
        (samePointSmall (prepared segment left owner request))
      (transportReserve segment left request)
    let query : TransportedQuery
        (polynomial.eval (segment.pointAt left.parameter))
        (prepared segment left owner request).track.initial.box :=
      { owner := queryOwner
        initial_box_refines :=
          ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines
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
          exact ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines
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

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Read the exact owner from the transported query at the requested local fraction. -/
@[expose] public def transportedAt {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Owner (polynomial.eval
      (segment.pointAt (parameterAt left request fraction))) :=
  (transportedQuery segment within left owner request ordered small fraction
    localInside).owner

/-- Variation from the source to an interpolated point is below the prepared source clearance. -/
public theorem pointVariationSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    ClearSheetContinuation.variationBound segment left.parameter
        (parameterAt left request fraction) <
      (prepared segment left owner request).track.initial.clearance.bound :=
  (ClearSheetContinuation.variationBound_le_of_between segment
    (parameterAt_between left request ordered fraction localInside).1
    (parameterAt_between left request ordered fraction localInside).2).trans_lt
      small

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The squared polynomial-value displacement to an interpolated point is below the prepared source clearance. -/
public theorem pointNormSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt left.parameter) -
          polynomial.eval
            (segment.pointAt (parameterAt left request fraction))) <
      (prepared segment left owner request).track.initial.clearance.bound :=
  (ClearSheetContinuation.evaluation_variation_le segment within
    left.parameter (parameterAt left request fraction) left.inside
      (parameterAt_inside left request ordered fraction localInside)).trans_lt
        (pointVariationSmall segment left owner request ordered small fraction
          localInside)

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- The query owner equals zero-reserve transport of the prepared source to the exact interpolated point. -/
public theorem transportedAt_eq_directAdvance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    transportedAt segment within left owner request ordered small fraction
        localInside =
      ExactQuadraticOwnerClearance.reservedTransport (prepared segment left owner request)
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

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The query owner's initial box refines the original prepared source box. -/
public theorem transportedAt_initial_box_refines
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (transportedAt segment within left owner request ordered small
      fraction localInside).track.initial.box.Refines
        (prepared segment left owner request).track.initial.box := by
  exact (transportedQuery segment within left owner request ordered small
    fraction localInside).initial_box_refines

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Every query anchor has squared displacement from the prepared anchor below the requested diameter. -/
public theorem transportedAt_anchor_distance_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (ordered : left.parameter <= request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound)
    (fraction : Coordinate)
    (localInside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Data.Gaussian.Norm.Basic.normSq
        ((transportedAt segment within left owner request ordered small
          fraction localInside).track.initial.box.anchor -
          (prepared segment left owner request).track.initial.box.anchor) <
      request.rootDiameter := by
  let parameter := parameterAt left request fraction
  have between := parameterAt_between left request ordered fraction localInside
  have localSmall :
      ClearSheetContinuation.variationBound segment
          left.parameter parameter <
        (prepared segment left owner request).track.initial.clearance.bound :=
    (ClearSheetContinuation.variationBound_le_of_between
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

section
open Purelib.Polynomial
open Purelib.Riemann.Branches
/-- Transport the prepared source to the requested endpoint and then retain or recondition it at the predicted reserve.

The result uses the exact transport owner as the input to reserve retention; root identity is preserved through both
operations. -/
@[expose] public def advance {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    Owner (polynomial.eval
      (segment.pointAt request.endpoint.parameter)) :=
  retainedAtReserve (transported segment within left owner request small)
    (preparedClearanceLower segment left request)

open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Advance using the retained prepared owner rather than recomputing its preparation.

Transport consumes the cache's exact owner and strict clearance evidence, followed by retention at the request's
predicted reserve. -/
@[expose] public def advanceCached {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound) :
    Owner (polynomial.eval
      (segment.pointAt request.endpoint.parameter)) :=
  retainedAtReserve
    (ExactQuadraticOwnerClearance.reservedTransport cached.preparedOwner
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      ((ClearSheetContinuation.evaluation_variation_le segment
        within left.parameter request.endpoint.parameter left.inside
          request.endpoint.inside).trans_lt small)
      (transportReserve segment left request))
    (preparedClearanceLower segment left request)

/-- Certified cached advancement equals canonical advancement for the same original owner and request. -/
public theorem advanceCached_eq_advance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (canonicalSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    advanceCached segment within left owner request cached cachedSmall =
      advance segment within left owner request canonicalSmall := by
  cases cached with
  | mk preparedOwner preparedOwner_eq =>
      cases preparedOwner_eq
      rfl

open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- A quadratic transport cache and derivative-margin bound make reserve retention leave the exact zero-reserve
transport unchanged. -/
public theorem advanceCached_eq_reservedTransport_of_quadraticCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (transportCache : ExactQuadraticOwnerClearance.QuadraticAmbientTransportCache cached.preparedOwner
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      ((ClearSheetContinuation.evaluation_variation_le segment
        within left.parameter request.endpoint.parameter left.inside
          request.endpoint.inside).trans_lt cachedSmall))
    (derivativeMarginLe :
      ClearSheetContinuation.squareRootDerivativeMargin segment ≤
        (1 / 4 : Coordinate)) :
    advanceCached segment within left owner request cached cachedSmall =
      ExactQuadraticOwnerClearance.reservedTransport cached.preparedOwner
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        ((ClearSheetContinuation.evaluation_variation_le segment
          within left.parameter request.endpoint.parameter left.inside
            request.endpoint.inside).trans_lt cachedSmall) 0 := by
  unfold advanceCached transportReserve
  apply retainedAtReserve_eq_self
  unfold preparedClearanceLower
  exact
    (UniformSquareRootPreparation.predictedClearance_le_transportFloor
      segment request.rootDiameter request.rootDiameterPositive
        derivativeMarginLe).trans transportCache.clearanceFloor

open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Exact box and clearance readings of cached advancement, with ambient dominance and the retained quadratic budget.

Each equality concerns the actual advanced owner and the given prepared cache. The five scalar bounds retain the four
ambient sides and their resulting clearance separately. -/
public structure ExactAmbientAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (leftBound rightBound bottomBound topBound clearanceBound : Coordinate) :
    Prop where
  /-- The actual advanced initial box equals the retained prepared source box. -/ initialBox :
    (advanceCached segment within left owner request cached
      cachedSmall).track.initial.box = cached.preparedOwner.track.initial.box
  /-- The actual advanced ambient box equals the retained prepared source ambient box. -/ ambientBox :
    (advanceCached segment within left owner request cached
      cachedSmall).ambient = cached.preparedOwner.ambient
  /-- The advanced owner's left ambient clearance equals the retained left bound. -/ ambientLeftBound :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientLeftClearance.bound = leftBound
  /-- The advanced owner's right ambient clearance equals the retained right bound. -/ ambientRightBound :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientRightClearance.bound = rightBound
  /-- The advanced owner's bottom ambient clearance equals the retained bottom bound. -/ ambientBottomBound :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientBottomClearance.bound = bottomBound
  /-- The advanced owner's top ambient clearance equals the retained top bound. -/ ambientTopBound :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientTopClearance.bound = topBound
  /-- The advanced owner's clearance equals the retained overall bound. -/ clearanceBound :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.clearance.bound = clearanceBound
  /-- The indexed owner's clearance is dominated by each of its retained ambient clearances. -/ dominance :
    ExactQuadraticOwnerClearance.AmbientClearanceDominance
    (advanceCached segment within left owner request cached cachedSmall)
  /-- The indexed owner retains the certified quadratic ambient budget. -/ budget :
    ExactQuadraticOwnerClearance.QuadraticAmbientBudget
    (advanceCached segment within left owner request cached cachedSmall)

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Derive exact cached-advance readings from the retained ambient transport cache and its four side equations.

The predicted reserve must fit the resulting clearance, and the target squared norm must be at most 256; these
conditions preserve the exact transport result and its quadratic budget. -/
public theorem exactAmbientAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    {leftSmall : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt left.parameter) -
        polynomial.eval (segment.pointAt request.endpoint.parameter)) <
      cached.preparedOwner.track.initial.ambientLeftClearance.bound}
    {rightSmall : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt left.parameter) -
        polynomial.eval (segment.pointAt request.endpoint.parameter)) <
      cached.preparedOwner.track.initial.ambientRightClearance.bound}
    {bottomSmall : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt left.parameter) -
        polynomial.eval (segment.pointAt request.endpoint.parameter)) <
      cached.preparedOwner.track.initial.ambientBottomClearance.bound}
    {topSmall : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt left.parameter) -
        polynomial.eval (segment.pointAt request.endpoint.parameter)) <
      cached.preparedOwner.track.initial.ambientTopClearance.bound}
    (transportCache : ExactQuadraticOwnerClearance.AmbientReservedTransportCache cached.preparedOwner
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      ((ClearSheetContinuation.evaluation_variation_le segment
        within left.parameter request.endpoint.parameter left.inside
          request.endpoint.inside).trans_lt cachedSmall)
      0 leftSmall rightSmall bottomSmall topSmall)
    (leftBound rightBound bottomBound topBound clearanceBound : Coordinate)
    (leftBoundEq :
      (ExactQuadraticOwnerClearance.ambientLeftAfterMove cached.preparedOwner leftSmall).bound = leftBound)
    (rightBoundEq :
      (ExactQuadraticOwnerClearance.ambientRightAfterMove cached.preparedOwner rightSmall).bound = rightBound)
    (bottomBoundEq :
      (ExactQuadraticOwnerClearance.ambientBottomAfterMove cached.preparedOwner bottomSmall).bound =
        bottomBound)
    (topBoundEq :
      (ExactQuadraticOwnerClearance.ambientTopAfterMove cached.preparedOwner topSmall).bound = topBound)
    (clearanceBoundEq :
      min leftBound (min rightBound (min bottomBound topBound)) =
        clearanceBound)
    (retained : preparedClearanceLower segment left request ≤ clearanceBound)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ExactAmbientAdvanceCache segment within left owner request cached
      cachedSmall leftBound rightBound bottomBound topBound clearanceBound := by
  have advanceEq :
      advanceCached segment within left owner request cached cachedSmall =
        ExactQuadraticOwnerClearance.reservedTransport cached.preparedOwner
          (segment.pointAt_eval_ne_zero request.endpoint.parameter
            request.endpoint.inside)
          ((ClearSheetContinuation.evaluation_variation_le segment
            within left.parameter request.endpoint.parameter left.inside
              request.endpoint.inside).trans_lt cachedSmall) 0 := by
    unfold advanceCached transportReserve
    apply retainedAtReserve_eq_self
    calc
      preparedClearanceLower segment left request ≤ clearanceBound := retained
      _ = min leftBound (min rightBound (min bottomBound topBound)) :=
        clearanceBoundEq.symm
      _ = min (ExactQuadraticOwnerClearance.ambientLeftAfterMove cached.preparedOwner leftSmall).bound
          (min (ExactQuadraticOwnerClearance.ambientRightAfterMove cached.preparedOwner rightSmall).bound
            (min
              (ExactQuadraticOwnerClearance.ambientBottomAfterMove cached.preparedOwner bottomSmall).bound
              (ExactQuadraticOwnerClearance.ambientTopAfterMove cached.preparedOwner topSmall).bound)) := by
        rw [leftBoundEq, rightBoundEq, bottomBoundEq, topBoundEq]
      _ = (ExactQuadraticOwnerClearance.reservedTransport cached.preparedOwner
          (segment.pointAt_eval_ne_zero request.endpoint.parameter
            request.endpoint.inside)
          ((ClearSheetContinuation.evaluation_variation_le segment
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
        leftSqLe := ?_
        rightSqLe := ?_
        bottomSqLe := ?_
        topSqLe := ?_ }
    · rw [transportCache.ambientBox]
      exact budget.verticalIntervalSqLe
    · rw [transportCache.ambientBox]
      exact budget.horizontalIntervalSqLe
    · rw [transportCache.initialBox]
      exact budget.leftSqLe
    · rw [transportCache.initialBox]
      exact budget.rightSqLe
    · rw [transportCache.initialBox]
      exact budget.bottomSqLe
    · rw [transportCache.initialBox]
      exact budget.topSqLe

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Box identities and quadratic clearance bounds for advancement at a retained margin floor.

The certificate retains the exact cached source, actual advanced owner, ambient dominance, and quadratic budget,
including separate side-clearance and overall-clearance upper bounds. -/
public structure ParametricQuadraticAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (marginFloor : Coordinate) : Prop where
  /-- The actual advanced initial box equals the retained prepared source box. -/ initialBox :
    (advanceCached segment within left owner request cached
      cachedSmall).track.initial.box = cached.preparedOwner.track.initial.box
  /-- The actual advanced ambient box equals the retained prepared source ambient box. -/ ambientBox :
    (advanceCached segment within left owner request cached
      cachedSmall).ambient = cached.preparedOwner.ambient
  /-- The specified quadratic transport floor is no greater than the indexed owner's clearance. -/ clearanceFloor :
    ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt marginFloor ≤
      (advanceCached segment within left owner request cached
        cachedSmall).track.initial.clearance.bound
  /-- The advanced left ambient clearance is at most one quarter of the squared source left clearance. -/
    ambientLeftQuarterSq :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientLeftClearance.bound ≤
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  /-- The advanced overall clearance is at most one quarter of the squared source left clearance. -/ clearanceQuarterSq
    :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.clearance.bound ≤
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  /-- The indexed owner's clearance is dominated by each of its retained ambient clearances. -/ dominance :
    ExactQuadraticOwnerClearance.AmbientClearanceDominance
    (advanceCached segment within left owner request cached cachedSmall)
  /-- The indexed owner retains the certified quadratic ambient budget. -/ budget :
    ExactQuadraticOwnerClearance.QuadraticAmbientBudget
    (advanceCached segment within left owner request cached cachedSmall)

section
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Certify cached advancement from a positive residual margin that pays the predicted transport floor.

The source and target polynomial values must differ, the source must retain ambient dominance and its quadratic budget,
and the target squared norm must be at most 256. -/
public theorem parametricQuadraticAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (marginFloor : Coordinate) (marginFloorPositive : 0 < marginFloor)
    (predictedLeFloor : preparedClearanceLower segment left request ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt marginFloor)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner)
    (marginLower : marginFloor ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricQuadraticAdvanceCache segment within left owner request cached
      cachedSmall marginFloor := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let moveSmall :=
    (ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt cachedSmall
  let transportCache :=
    ExactQuadraticOwnerClearance.parametricQuadraticAmbientTransportCache
      cached.preparedOwner targetNonzero moveSmall different dominance
        marginFloor marginFloorPositive marginLower budget targetNormSqLe
  have advanceEq :
      advanceCached segment within left owner request cached cachedSmall =
        ExactQuadraticOwnerClearance.reservedTransport cached.preparedOwner targetNonzero moveSmall 0 := by
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

/-- Certify advancement by a retained-floor tradeoff between residual margin and side majorants.

The positive residual floor and exact side upper bound must pay the requested quadratic transport floor through the
stated squared-margin inequality. -/
public theorem retainedFloorQuadraticAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (retainedFloor residualFloor sideUpper : Coordinate)
    (predictedLeFloor : preparedClearanceLower segment left request ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt retainedFloor)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner)
    (residualFloorPositive : 0 < residualFloor)
    (marginLower : residualFloor ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (sideBounds : ExactQuadraticOwnerClearance.QuadraticAmbientSideMajorantBounds cached.preparedOwner
      sideUpper)
    (tradeoff : ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt retainedFloor ≤
      residualFloor ^ 2 / (4 * sideUpper))
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricQuadraticAdvanceCache segment within left owner request cached
      cachedSmall retainedFloor := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let moveSmall :=
    (ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt cachedSmall
  let transportCache :=
    ExactQuadraticOwnerClearance.retainedFloorQuadraticAmbientTransportCache
      cached.preparedOwner targetNonzero moveSmall different dominance
        retainedFloor residualFloor sideUpper residualFloorPositive marginLower
          sideBounds tradeoff budget targetNormSqLe
  have advanceEq :
      advanceCached segment within left owner request cached cachedSmall =
        ExactQuadraticOwnerClearance.reservedTransport cached.preparedOwner targetNonzero moveSmall 0 := by
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

/-- A residual margin of at least one sixteenth certifies advancement at the quadratic floor associated with one eighth.

The predicted reserve must fit that floor; retain the source dominance and quadratic budget, distinct endpoint values,
and the target squared-norm bound of 256. -/
public theorem eighthFloorQuadraticAdvanceCache_of_sixteenthMargin
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (predictedLeEighthFloor : preparedClearanceLower segment left request ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner)
    (sixteenthMarginLower : (1 : Coordinate) / 16 ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricQuadraticAdvanceCache segment within left owner request cached
      cachedSmall (1 / 8 : Coordinate) := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let moveSmall :=
    (ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt cachedSmall
  let transportCache :=
    ExactQuadraticOwnerClearance.eighthFloorQuadraticAmbientTransportCache_of_sixteenthMargin
      cached.preparedOwner targetNonzero moveSmall different dominance
        sixteenthMarginLower budget targetNormSqLe
  have advanceEq :
      advanceCached segment within left owner request cached cachedSmall =
        ExactQuadraticOwnerClearance.reservedTransport cached.preparedOwner targetNonzero moveSmall 0 := by
    unfold advanceCached transportReserve
    apply retainedAtReserve_eq_self
    exact predictedLeEighthFloor.trans transportCache.clearanceFloor
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

/-- A one-over-128 residual margin and side majorants bounded by 256 certify advancement at the one-eighth quadratic
floor. -/
public theorem eighthFloorQuadraticAdvanceCache_of_oneTwentyEighthMargin
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (predictedLeEighthFloor : preparedClearanceLower segment left request ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner)
    (marginLower : (1 : Coordinate) / 128 ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (sideBounds : ExactQuadraticOwnerClearance.QuadraticAmbientSideMajorantBounds
      cached.preparedOwner 256)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricQuadraticAdvanceCache segment within left owner request cached
      cachedSmall (1 / 8 : Coordinate) := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let moveSmall :=
    (ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt cachedSmall
  let transportCache :=
    ExactQuadraticOwnerClearance.eighthFloorQuadraticAmbientTransportCache_of_oneTwentyEighthMargin
      cached.preparedOwner targetNonzero moveSmall different dominance
        marginLower sideBounds budget targetNormSqLe
  have advanceEq :
      advanceCached segment within left owner request cached cachedSmall =
        ExactQuadraticOwnerClearance.reservedTransport cached.preparedOwner targetNonzero moveSmall 0 := by
    unfold advanceCached transportReserve
    apply retainedAtReserve_eq_self
    exact predictedLeEighthFloor.trans transportCache.clearanceFloor
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

/-- A three-over-256 residual margin and side majorants bounded by 512 certify advancement at the one-eighth quadratic
floor. -/
public theorem eighthFloorQuadraticAdvanceCache_of_threeTwoFiftySixthMargin
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (predictedLeEighthFloor : preparedClearanceLower segment left request ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner)
    (marginLower : (3 : Coordinate) / 256 ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (sideBounds : ExactQuadraticOwnerClearance.QuadraticAmbientSideMajorantBounds
      cached.preparedOwner 512)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricQuadraticAdvanceCache segment within left owner request cached
      cachedSmall (1 / 8 : Coordinate) := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let moveSmall :=
    (ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt cachedSmall
  let transportCache :=
    ExactQuadraticOwnerClearance.eighthFloorQuadraticAmbientTransportCache_of_threeTwoFiftySixthMargin
      cached.preparedOwner targetNonzero moveSmall different dominance
        marginLower sideBounds budget targetNormSqLe
  have advanceEq :
      advanceCached segment within left owner request cached cachedSmall =
        ExactQuadraticOwnerClearance.reservedTransport cached.preparedOwner targetNonzero moveSmall 0 := by
    unfold advanceCached transportReserve
    apply retainedAtReserve_eq_self
    exact predictedLeEighthFloor.trans transportCache.clearanceFloor
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

/-- A one-over-64 residual margin and side majorants bounded by 1024 certify advancement at the one-eighth quadratic
floor. -/
public theorem eighthFloorQuadraticAdvanceCache_of_sixtyFourthMargin
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (predictedLeEighthFloor : preparedClearanceLower segment left request ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner)
    (marginLower : (1 : Coordinate) / 64 ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (sideBounds : ExactQuadraticOwnerClearance.QuadraticAmbientSideMajorantBounds
      cached.preparedOwner 1024)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricQuadraticAdvanceCache segment within left owner request cached
      cachedSmall (1 / 8 : Coordinate) := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let moveSmall :=
    (ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt cachedSmall
  let transportCache :=
    ExactQuadraticOwnerClearance.eighthFloorQuadraticAmbientTransportCache_of_sixtyFourthMargin
      cached.preparedOwner targetNonzero moveSmall different dominance
        marginLower sideBounds budget targetNormSqLe
  have advanceEq :
      advanceCached segment within left owner request cached cachedSmall =
        ExactQuadraticOwnerClearance.reservedTransport cached.preparedOwner targetNonzero moveSmall 0 := by
    unfold advanceCached transportReserve
    apply retainedAtReserve_eq_self
    exact predictedLeEighthFloor.trans transportCache.clearanceFloor
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

end

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- A root owner retaining a fixed initial box, transport floor, ambient dominance, budget, and side upper bound.

Its exact ambient box refines the retained box; these data allow successive certified steps to keep the same box
identity. -/
public structure ParametricSameBoxState
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (box : Box) (preparedUpper marginFloor : Coordinate) : Prop where
  /-- The current owner's initial box is exactly the retained box. -/ boxEq : owner.track.initial.box = box
  /-- The specified quadratic transport floor is no greater than the indexed owner's clearance. -/ clearanceFloor :
    ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt marginFloor ≤
    owner.track.initial.clearance.bound
  /-- The indexed owner's clearance is dominated by each of its retained ambient clearances. -/ dominance :
    ExactQuadraticOwnerClearance.AmbientClearanceDominance owner
  /-- The indexed owner retains the certified quadratic ambient budget. -/ budget :
    ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner
  /-- The current left ambient clearance is at most the retained prepared upper bound. -/ ambientLeftLe :
    owner.track.initial.ambientLeftClearance.bound ≤ preparedUpper
  /-- The current ambient box refines the retained fixed box. -/ ambientRefines : owner.ambient.Refines box

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Certificates for advancing a prepared source while retaining the exact fixed root box.

The step retains readiness, a carrying strengthened candidate, the canonical cache and advance certificate, and the next
owner's box, ambient refinement, and quarter-square side bound. -/
public structure ParametricSameBoxStep
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box)
    (directLower preparedUpper marginFloor : Coordinate) : Prop where
  /-- The retained owner satisfies the requested diameter, clearance floor, and root-ambient conditions. -/ ready :
    AlreadyPrepared segment left owner request
  /-- Exact quadratic strengthening of the source has enough clearance for the requested variation. -/
    strengthenedCarries :
    ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter <
      (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound
  /-- The actual canonical prepared source has enough clearance for the requested variation. -/ canonicalSmall :
    ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter <
      (prepared segment left owner request).track.initial.clearance.bound
  /-- The canonical cached source's left ambient clearance is at most the retained upper bound. -/ preparedAmbientLeftLe
    :
    (CachedSource.canonical segment left owner request).preparedOwner.track.initial.ambientLeftClearance.bound ≤
      preparedUpper
  /-- The quantitative certificate for advancing this exact canonical cached source. -/ advanceCache :
    ParametricQuadraticAdvanceCache segment within left owner
    request (CachedSource.canonical segment left owner request) canonicalSmall
      marginFloor
  /-- The actual next owner's initial box equals the retained fixed box. -/ nextOwnerBox :
    (advanceCached segment within left owner request
      (CachedSource.canonical segment left owner request)
        canonicalSmall).track.initial.box = box
  /-- The next left ambient clearance is at most one quarter of the squared retained upper bound. -/
    nextAmbientLeftLeQuarter :
    (advanceCached segment within left owner request
      (CachedSource.canonical segment left owner request)
        canonicalSmall).track.initial.ambientLeftClearance.bound ≤
      preparedUpper ^ 2 / 4
  /-- The actual next ambient box refines the original owner's ambient box. -/ nextAmbientRefines :
    (advanceCached segment within left owner request
      (CachedSource.canonical segment left owner request)
        canonicalSmall).ambient.Refines owner.ambient

namespace ParametricSameBoxStep

open Purelib.Polynomial
/-- Read the exact cached-advance owner certified by the retained same-box step. -/
@[expose] public def nextOwner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    {request : StepRequest} {box : Box}
    {directLower preparedUpper marginFloor : Coordinate}
    (step : ParametricSameBoxStep segment within left owner request box
      directLower preparedUpper marginFloor) :
    Owner (polynomial.eval (segment.pointAt request.endpoint.parameter)) :=
  advanceCached segment within left owner request
    (CachedSource.canonical segment left owner request) step.canonicalSmall

/-- Transport a retained same-box state through its certified step when the quarter-square upper bound fits the original
upper bound. -/
public theorem nextState
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt left.parameter))}
    {request : StepRequest} {box : Box}
    {directLower preparedUpper marginFloor : Coordinate}
    (step : ParametricSameBoxStep segment within left owner request box
      directLower preparedUpper marginFloor)
    (state : ParametricSameBoxState segment left owner box preparedUpper
      marginFloor)
    (quarterSquareLe : preparedUpper ^ 2 / 4 ≤ preparedUpper) :
    ParametricSameBoxState segment request.endpoint step.nextOwner box
      preparedUpper marginFloor :=
  { boxEq := step.nextOwnerBox
    clearanceFloor := step.advanceCache.clearanceFloor
    dominance := step.advanceCache.dominance
    budget := step.advanceCache.budget
    ambientLeftLe := step.nextAmbientLeftLeQuarter.trans quarterSquareLe
    ambientRefines := step.nextAmbientRefines.trans state.ambientRefines }

end ParametricSameBoxStep

section
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Construct a same-box step from direct boundary bounds and a positive residual margin.

Readiness comes from the retained box, clearance floor, and root-ambient refinement; the direct lower bound carries the
move while the margin pays the prescribed transport floor. -/
public theorem parametricSameBoxStep
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box)
    (boxEq : owner.track.initial.box = box)
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (currentFloor : Coordinate)
    (predictedLeCurrent :
      preparedClearanceLower segment left request ≤ currentFloor)
    (currentFloorLe : currentFloor ≤ owner.track.initial.clearance.bound)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner)
    (directLower preparedUpper : Coordinate)
    (ownerAmbientLeftLe :
      owner.track.initial.ambientLeftClearance.bound ≤ preparedUpper)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (marginFloor : Coordinate) (marginFloorPositive : 0 < marginFloor)
    (predictedLeTransportFloor :
      preparedClearanceLower segment left request ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt marginFloor)
    (variationMargin : marginFloor ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper marginFloor := by
  have ready : AlreadyPrepared segment left owner request :=
    ⟨boxEq ▸ boxSmall, predictedLeCurrent.trans currentFloorLe,
      boxEq ▸ boxRefines⟩
  let actualCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter))
      owner.track.initial.box directLower preparedUpper := by
    rw [boxEq]
    exact directCache
  have strengthenedCarries :
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound :=
    (variationLtDirectLower.trans_le actualCache.lower_le).trans_le
      (ExactQuadraticOwnerClearance.directBoundaryClearance_le_strengthenQuadraticOwner owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero)
  have canonicalSmall :=
    variation_lt_prepared_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries
  let cached := CachedSource.canonical segment left owner request
  have preparedDominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner :=
    prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries dominance
  have preparedBudget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner :=
    prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries budget
  have preparedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        preparedUpper := by
    change (prepared segment left owner request).track.initial.ambientLeftClearance.bound ≤
      preparedUpper
    by_cases carries :
        ClearSheetContinuation.variationBound segment
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
      rw [leftEq, ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero]
      exact Fraction.Order.Basic.max_le (dominance.left.trans ownerAmbientLeftLe)
        actualCache.le_upper
  have preparedMargin : marginFloor ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
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
    Fraction.Order.Arithmetic.pow_le_pow_direct
      cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
        preparedAmbientLeftLe 2
  have quarterSquareLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        preparedUpper ^ 2 / 4 := by
    change
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
          (4 : Coordinate)⁻¹ ≤
        preparedUpper ^ 2 * (4 : Coordinate)⁻¹
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      preparedSquareLe
        (Fraction.Order.Field.inv_pos_direct (by decide)).le
  have nextAmbientLeftLeQuarter :=
    advanceCache.ambientLeftQuarterSq.trans quarterSquareLe
  have preparedAmbientRefines : cached.preparedOwner.ambient.Refines
      owner.ambient := by
    change (prepared segment left owner request).ambient.Refines owner.ambient
    by_cases carries :
        ClearSheetContinuation.variationBound segment
            left.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound
    · rw [prepared_eq_self_of_ready segment left owner request ready carries]
      exact Box.refines_refl _
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment left owner
        request ready carries strengthenedCarries]
      exact ExactQuadraticOwnerClearance.strengthenQuadraticOwner_ambient_refines owner
  have nextAmbientRefines :
      (advanceCached segment within left owner request cached
        canonicalSmall).ambient.Refines owner.ambient := by
    rw [advanceCache.ambientBox]
    exact preparedAmbientRefines
  exact ⟨ready, strengthenedCarries, canonicalSmall, preparedAmbientLeftLe,
    advanceCache, nextOwnerBox, nextAmbientLeftLeQuarter,
      nextAmbientRefines⟩

/-- Construct a same-box step at the one-eighth quadratic floor from a one-sixteenth variation margin.

Retain the original box, direct boundary bounds, source budget and dominance, and distinct endpoint values with target
squared norm at most 256. -/
public theorem eighthFloorSameBoxStepOfSixteenthMargin
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box)
    (boxEq : owner.track.initial.box = box)
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (predictedLeEighthFloor :
      preparedClearanceLower segment left request ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (eighthFloorLeCurrent :
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
        owner.track.initial.clearance.bound)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner)
    (directLower preparedUpper : Coordinate)
    (ownerAmbientLeftLe :
      owner.track.initial.ambientLeftClearance.bound ≤ preparedUpper)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (variationMargin : (1 : Coordinate) / 16 ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper (1 / 8 : Coordinate) := by
  have ready : AlreadyPrepared segment left owner request :=
    ⟨boxEq ▸ boxSmall,
      predictedLeEighthFloor.trans eighthFloorLeCurrent,
      boxEq ▸ boxRefines⟩
  let actualCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter))
      owner.track.initial.box directLower preparedUpper := by
    rw [boxEq]
    exact directCache
  have strengthenedCarries :
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound :=
    (variationLtDirectLower.trans_le actualCache.lower_le).trans_le
      (ExactQuadraticOwnerClearance.directBoundaryClearance_le_strengthenQuadraticOwner owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero)
  have canonicalSmall :=
    variation_lt_prepared_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries
  let cached := CachedSource.canonical segment left owner request
  have preparedDominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner :=
    prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries dominance
  have preparedBudget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner :=
    prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries budget
  have preparedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        preparedUpper := by
    change (prepared segment left owner request).track.initial.ambientLeftClearance.bound ≤
      preparedUpper
    by_cases carries :
        ClearSheetContinuation.variationBound segment
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
      rw [leftEq, ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero]
      exact Fraction.Order.Basic.max_le (dominance.left.trans ownerAmbientLeftLe)
        actualCache.le_upper
  have preparedMargin : (1 : Coordinate) / 16 ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) :=
    prepared_margin_lower_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries (1 / 16 : Coordinate) _
        variationMargin
  have advanceCache : ParametricQuadraticAdvanceCache segment within left owner
      request cached canonicalSmall (1 / 8 : Coordinate) := by
    apply eighthFloorQuadraticAdvanceCache_of_sixteenthMargin segment within
      left owner request cached canonicalSmall different
        predictedLeEighthFloor preparedDominance preparedMargin preparedBudget
          targetNormSqLe
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
    Fraction.Order.Arithmetic.pow_le_pow_direct
      cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
        preparedAmbientLeftLe 2
  have quarterSquareLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        preparedUpper ^ 2 / 4 := by
    change
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
          (4 : Coordinate)⁻¹ ≤
        preparedUpper ^ 2 * (4 : Coordinate)⁻¹
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      preparedSquareLe
        (Fraction.Order.Field.inv_pos_direct (by decide)).le
  have nextAmbientLeftLeQuarter :=
    advanceCache.ambientLeftQuarterSq.trans quarterSquareLe
  have preparedAmbientRefines : cached.preparedOwner.ambient.Refines
      owner.ambient := by
    change (prepared segment left owner request).ambient.Refines owner.ambient
    by_cases carries :
        ClearSheetContinuation.variationBound segment
            left.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound
    · rw [prepared_eq_self_of_ready segment left owner request ready carries]
      exact Box.refines_refl _
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment left owner
        request ready carries strengthenedCarries]
      exact ExactQuadraticOwnerClearance.strengthenQuadraticOwner_ambient_refines owner
  have nextAmbientRefines :
      (advanceCached segment within left owner request cached
        canonicalSmall).ambient.Refines owner.ambient := by
    rw [advanceCache.ambientBox]
    exact preparedAmbientRefines
  exact ⟨ready, strengthenedCarries, canonicalSmall, preparedAmbientLeftLe,
    advanceCache, nextOwnerBox, nextAmbientLeftLeQuarter,
      nextAmbientRefines⟩

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Construct the one-sixteenth-margin step using the box, floor, dominance, and budget already retained by a same-box
state. -/
public theorem eighthFloorSameBoxStepOfSixteenthMarginFromState
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box) (preparedUpper : Coordinate)
    (state : ParametricSameBoxState segment left owner box preparedUpper
      (1 / 8 : Coordinate))
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (predictedLeEighthFloor :
      preparedClearanceLower segment left request ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (directLower : Coordinate)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (variationMargin : (1 : Coordinate) / 16 ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper (1 / 8 : Coordinate) :=
  eighthFloorSameBoxStepOfSixteenthMargin segment within left owner request
    box state.boxEq boxSmall boxRefines predictedLeEighthFloor
      state.clearanceFloor state.dominance state.budget directLower
        preparedUpper state.ambientLeftLe directCache variationLtDirectLower
          different variationMargin targetNormSqLe

section
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Construct a same-box step at the one-eighth floor using a one-over-128 variation margin and box-side majorants
bounded by 256. -/
public theorem eighthFloorSameBoxStepOfOneTwentyEighthMargin
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box)
    (boxEq : owner.track.initial.box = box)
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (predictedLeEighthFloor :
      preparedClearanceLower segment left request ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (eighthFloorLeCurrent :
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
        owner.track.initial.clearance.bound)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner)
    (directLower preparedUpper : Coordinate)
    (ownerAmbientLeftLe :
      owner.track.initial.ambientLeftClearance.bound ≤ preparedUpper)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (variationMargin : (1 : Coordinate) / 128 ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (ownerAmbientRefines : owner.ambient.Refines box)
    (boxSideBounds : ExactQuadraticOwnerClearance.QuadraticBoxSideMajorantBounds
      (polynomial.eval (segment.pointAt left.parameter)) box 256)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper (1 / 8 : Coordinate) := by
  have ready : AlreadyPrepared segment left owner request :=
    ⟨boxEq ▸ boxSmall,
      predictedLeEighthFloor.trans eighthFloorLeCurrent,
      boxEq ▸ boxRefines⟩
  let actualCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter))
      owner.track.initial.box directLower preparedUpper := by
    rw [boxEq]
    exact directCache
  have strengthenedCarries :
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound :=
    (variationLtDirectLower.trans_le actualCache.lower_le).trans_le
      (ExactQuadraticOwnerClearance.directBoundaryClearance_le_strengthenQuadraticOwner owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero)
  have canonicalSmall :=
    variation_lt_prepared_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries
  let cached := CachedSource.canonical segment left owner request
  have preparedDominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner :=
    prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries dominance
  have preparedBudget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner :=
    prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries budget
  have preparedAmbientRefines : cached.preparedOwner.ambient.Refines
      owner.ambient := by
    change (prepared segment left owner request).ambient.Refines owner.ambient
    by_cases carries :
        ClearSheetContinuation.variationBound segment
            left.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound
    · rw [prepared_eq_self_of_ready segment left owner request ready carries]
      exact Box.refines_refl _
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment left owner
        request ready carries strengthenedCarries]
      exact ExactQuadraticOwnerClearance.strengthenQuadraticOwner_ambient_refines owner
  have preparedBoxEq : cached.preparedOwner.track.initial.box = box :=
    (prepared_initial_box_eq_of_ready_of_strengthenedCarries segment left
      owner request ready strengthenedCarries).trans boxEq
  have preparedSideBounds : ExactQuadraticOwnerClearance.QuadraticAmbientSideMajorantBounds
      cached.preparedOwner 256 :=
    ExactQuadraticOwnerClearance.quadraticAmbientSideMajorantBounds_of_box cached.preparedOwner box 256
      preparedBoxEq (preparedAmbientRefines.trans ownerAmbientRefines)
        boxSideBounds
  have preparedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        preparedUpper := by
    change (prepared segment left owner request).track.initial.ambientLeftClearance.bound ≤
      preparedUpper
    by_cases carries :
        ClearSheetContinuation.variationBound segment
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
      rw [leftEq, ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero]
      exact Fraction.Order.Basic.max_le (dominance.left.trans ownerAmbientLeftLe)
        actualCache.le_upper
  have preparedMargin : (1 : Coordinate) / 128 ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) :=
    prepared_margin_lower_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries (1 / 128 : Coordinate) _
        variationMargin
  have advanceCache : ParametricQuadraticAdvanceCache segment within left owner
      request cached canonicalSmall (1 / 8 : Coordinate) := by
    apply eighthFloorQuadraticAdvanceCache_of_oneTwentyEighthMargin segment
      within left owner request cached canonicalSmall different
        predictedLeEighthFloor preparedDominance preparedMargin
          preparedSideBounds preparedBudget targetNormSqLe
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
    Fraction.Order.Arithmetic.pow_le_pow_direct
      cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
        preparedAmbientLeftLe 2
  have quarterSquareLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        preparedUpper ^ 2 / 4 := by
    change
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
          (4 : Coordinate)⁻¹ ≤
        preparedUpper ^ 2 * (4 : Coordinate)⁻¹
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      preparedSquareLe
        (Fraction.Order.Field.inv_pos_direct (by decide)).le
  have nextAmbientLeftLeQuarter :=
    advanceCache.ambientLeftQuarterSq.trans quarterSquareLe
  have nextAmbientRefines :
      (advanceCached segment within left owner request cached
        canonicalSmall).ambient.Refines owner.ambient := by
    rw [advanceCache.ambientBox]
    exact preparedAmbientRefines
  exact ⟨ready, strengthenedCarries, canonicalSmall, preparedAmbientLeftLe,
    advanceCache, nextOwnerBox, nextAmbientLeftLeQuarter,
      nextAmbientRefines⟩

/-- Construct a same-box step from explicit residual and box-side bounds satisfying the retained-floor tradeoff.

All generated numerical bounds are supplied as certified hypotheses on the exact source and box; the construction
retains the source cache and resulting owner identities. -/
public theorem retainedFloorSameBoxStepOfGeneratedBounds
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box)
    (boxEq : owner.track.initial.box = box)
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (marginFloor : Coordinate)
    (predictedLeTransportFloor :
      preparedClearanceLower segment left request ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt marginFloor)
    (transportFloorLeCurrent :
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt marginFloor ≤
        owner.track.initial.clearance.bound)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner)
    (directLower preparedUpper : Coordinate)
    (ownerAmbientLeftLe :
      owner.track.initial.ambientLeftClearance.bound ≤ preparedUpper)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (residualFloor sideUpper : Coordinate)
    (residualFloorPositive : 0 < residualFloor)
    (variationMargin : residualFloor ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (ownerAmbientRefines : owner.ambient.Refines box)
    (boxSideBounds : ExactQuadraticOwnerClearance.QuadraticBoxSideMajorantBounds
      (polynomial.eval (segment.pointAt left.parameter)) box sideUpper)
    (tradeoff : ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt marginFloor ≤
      residualFloor ^ 2 / (4 * sideUpper))
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper marginFloor := by
  have ready : AlreadyPrepared segment left owner request :=
    ⟨boxEq ▸ boxSmall,
      predictedLeTransportFloor.trans transportFloorLeCurrent,
      boxEq ▸ boxRefines⟩
  let actualCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter))
      owner.track.initial.box directLower preparedUpper := by
    rw [boxEq]
    exact directCache
  have strengthenedCarries :
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound :=
    (variationLtDirectLower.trans_le actualCache.lower_le).trans_le
      (ExactQuadraticOwnerClearance.directBoundaryClearance_le_strengthenQuadraticOwner owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero)
  have canonicalSmall :=
    variation_lt_prepared_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries
  let cached := CachedSource.canonical segment left owner request
  have preparedDominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner :=
    prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries dominance
  have preparedBudget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner :=
    prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries budget
  have preparedAmbientRefines : cached.preparedOwner.ambient.Refines
      owner.ambient := by
    change (prepared segment left owner request).ambient.Refines owner.ambient
    by_cases carries :
        ClearSheetContinuation.variationBound segment
            left.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound
    · rw [prepared_eq_self_of_ready segment left owner request ready carries]
      exact Box.refines_refl _
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment left owner
        request ready carries strengthenedCarries]
      exact ExactQuadraticOwnerClearance.strengthenQuadraticOwner_ambient_refines owner
  have preparedBoxEq : cached.preparedOwner.track.initial.box = box :=
    (prepared_initial_box_eq_of_ready_of_strengthenedCarries segment left
      owner request ready strengthenedCarries).trans boxEq
  have preparedSideBounds : ExactQuadraticOwnerClearance.QuadraticAmbientSideMajorantBounds
      cached.preparedOwner sideUpper :=
    ExactQuadraticOwnerClearance.quadraticAmbientSideMajorantBounds_of_box cached.preparedOwner box
      sideUpper preparedBoxEq
        (preparedAmbientRefines.trans ownerAmbientRefines) boxSideBounds
  have preparedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        preparedUpper := by
    change (prepared segment left owner request).track.initial.ambientLeftClearance.bound ≤
      preparedUpper
    by_cases carries :
        ClearSheetContinuation.variationBound segment
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
      rw [leftEq, ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero]
      exact Fraction.Order.Basic.max_le (dominance.left.trans ownerAmbientLeftLe)
        actualCache.le_upper
  have preparedMargin : residualFloor ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) :=
    prepared_margin_lower_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries residualFloor _ variationMargin
  have advanceCache : ParametricQuadraticAdvanceCache segment within left owner
      request cached canonicalSmall marginFloor := by
    exact retainedFloorQuadraticAdvanceCache segment within left owner request
      cached canonicalSmall different marginFloor residualFloor sideUpper
        predictedLeTransportFloor preparedDominance residualFloorPositive
          preparedMargin preparedSideBounds tradeoff
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
    Fraction.Order.Arithmetic.pow_le_pow_direct
      cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
        preparedAmbientLeftLe 2
  have quarterSquareLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        preparedUpper ^ 2 / 4 := by
    change
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
          (4 : Coordinate)⁻¹ ≤
        preparedUpper ^ 2 * (4 : Coordinate)⁻¹
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      preparedSquareLe
        (Fraction.Order.Field.inv_pos_direct (by decide)).le
  have nextAmbientLeftLeQuarter :=
    advanceCache.ambientLeftQuarterSq.trans quarterSquareLe
  have nextAmbientRefines :
      (advanceCached segment within left owner request cached
        canonicalSmall).ambient.Refines owner.ambient := by
    rw [advanceCache.ambientBox]
    exact preparedAmbientRefines
  exact ⟨ready, strengthenedCarries, canonicalSmall, preparedAmbientLeftLe,
    advanceCache, nextOwnerBox, nextAmbientLeftLeQuarter,
      nextAmbientRefines⟩

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Construct the explicit-bound same-box step using the original state's retained box, clearance, dominance, budget,
and ambient refinement. -/
public theorem retainedFloorSameBoxStepOfGeneratedBoundsFromState
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box) (preparedUpper : Coordinate)
    (marginFloor : Coordinate)
    (state : ParametricSameBoxState segment left owner box preparedUpper
      marginFloor)
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (predictedLeTransportFloor : preparedClearanceLower segment left request ≤
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt marginFloor)
    (directLower : Coordinate)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (residualFloor sideUpper : Coordinate)
    (residualFloorPositive : 0 < residualFloor)
    (variationMargin : residualFloor ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (boxSideBounds : ExactQuadraticOwnerClearance.QuadraticBoxSideMajorantBounds
      (polynomial.eval (segment.pointAt left.parameter)) box sideUpper)
    (tradeoff : ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt marginFloor ≤
      residualFloor ^ 2 / (4 * sideUpper))
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper marginFloor :=
  retainedFloorSameBoxStepOfGeneratedBounds segment within left owner request
    box state.boxEq boxSmall boxRefines marginFloor predictedLeTransportFloor
      state.clearanceFloor state.dominance state.budget directLower
        preparedUpper state.ambientLeftLe directCache variationLtDirectLower
          different residualFloor sideUpper residualFloorPositive
            variationMargin state.ambientRefines boxSideBounds tradeoff
              targetNormSqLe

section
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Construct a same-box step at the one-eighth floor using a three-over-256 variation margin and box-side majorants
bounded by 512. -/
public theorem eighthFloorSameBoxStepOfThreeTwoFiftySixthMargin
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box)
    (boxEq : owner.track.initial.box = box)
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (predictedLeEighthFloor :
      preparedClearanceLower segment left request ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (eighthFloorLeCurrent :
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
        owner.track.initial.clearance.bound)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner)
    (directLower preparedUpper : Coordinate)
    (ownerAmbientLeftLe :
      owner.track.initial.ambientLeftClearance.bound ≤ preparedUpper)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (variationMargin : (3 : Coordinate) / 256 ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (ownerAmbientRefines : owner.ambient.Refines box)
    (boxSideBounds : ExactQuadraticOwnerClearance.QuadraticBoxSideMajorantBounds
      (polynomial.eval (segment.pointAt left.parameter)) box 512)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper (1 / 8 : Coordinate) := by
  have ready : AlreadyPrepared segment left owner request :=
    ⟨boxEq ▸ boxSmall,
      predictedLeEighthFloor.trans eighthFloorLeCurrent,
      boxEq ▸ boxRefines⟩
  let actualCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter))
      owner.track.initial.box directLower preparedUpper := by
    rw [boxEq]
    exact directCache
  have strengthenedCarries :
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound :=
    (variationLtDirectLower.trans_le actualCache.lower_le).trans_le
      (ExactQuadraticOwnerClearance.directBoundaryClearance_le_strengthenQuadraticOwner owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero)
  have canonicalSmall :=
    variation_lt_prepared_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries
  let cached := CachedSource.canonical segment left owner request
  have preparedDominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner :=
    prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries dominance
  have preparedBudget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner :=
    prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries budget
  have preparedAmbientRefines : cached.preparedOwner.ambient.Refines
      owner.ambient := by
    change (prepared segment left owner request).ambient.Refines owner.ambient
    by_cases carries :
        ClearSheetContinuation.variationBound segment
            left.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound
    · rw [prepared_eq_self_of_ready segment left owner request ready carries]
      exact Box.refines_refl _
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment left owner
        request ready carries strengthenedCarries]
      exact ExactQuadraticOwnerClearance.strengthenQuadraticOwner_ambient_refines owner
  have preparedBoxEq : cached.preparedOwner.track.initial.box = box :=
    (prepared_initial_box_eq_of_ready_of_strengthenedCarries segment left
      owner request ready strengthenedCarries).trans boxEq
  have preparedSideBounds : ExactQuadraticOwnerClearance.QuadraticAmbientSideMajorantBounds
      cached.preparedOwner 512 :=
    ExactQuadraticOwnerClearance.quadraticAmbientSideMajorantBounds_of_box cached.preparedOwner box 512
      preparedBoxEq (preparedAmbientRefines.trans ownerAmbientRefines)
        boxSideBounds
  have preparedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        preparedUpper := by
    change (prepared segment left owner request).track.initial.ambientLeftClearance.bound ≤
      preparedUpper
    by_cases carries :
        ClearSheetContinuation.variationBound segment
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
      rw [leftEq, ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero]
      exact Fraction.Order.Basic.max_le (dominance.left.trans ownerAmbientLeftLe)
        actualCache.le_upper
  have preparedMargin : (3 : Coordinate) / 256 ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) :=
    prepared_margin_lower_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries (3 / 256 : Coordinate) _
        variationMargin
  have advanceCache : ParametricQuadraticAdvanceCache segment within left owner
      request cached canonicalSmall (1 / 8 : Coordinate) := by
    apply eighthFloorQuadraticAdvanceCache_of_threeTwoFiftySixthMargin segment
      within left owner request cached canonicalSmall different
        predictedLeEighthFloor preparedDominance preparedMargin
          preparedSideBounds preparedBudget targetNormSqLe
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
    Fraction.Order.Arithmetic.pow_le_pow_direct
      cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
        preparedAmbientLeftLe 2
  have quarterSquareLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        preparedUpper ^ 2 / 4 := by
    change
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
          (4 : Coordinate)⁻¹ ≤
        preparedUpper ^ 2 * (4 : Coordinate)⁻¹
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      preparedSquareLe
        (Fraction.Order.Field.inv_pos_direct (by decide)).le
  have nextAmbientLeftLeQuarter :=
    advanceCache.ambientLeftQuarterSq.trans quarterSquareLe
  have nextAmbientRefines :
      (advanceCached segment within left owner request cached
        canonicalSmall).ambient.Refines owner.ambient := by
    rw [advanceCache.ambientBox]
    exact preparedAmbientRefines
  exact ⟨ready, strengthenedCarries, canonicalSmall, preparedAmbientLeftLe,
    advanceCache, nextOwnerBox, nextAmbientLeftLeQuarter,
      nextAmbientRefines⟩

/-- Construct a same-box step at the one-eighth floor using a one-over-64 variation margin and box-side majorants
bounded by 1024. -/
public theorem eighthFloorSameBoxStepOfSixtyFourthMargin
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box)
    (boxEq : owner.track.initial.box = box)
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (predictedLeEighthFloor :
      preparedClearanceLower segment left request ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (eighthFloorLeCurrent :
      ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate) ≤
        owner.track.initial.clearance.bound)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner)
    (directLower preparedUpper : Coordinate)
    (ownerAmbientLeftLe :
      owner.track.initial.ambientLeftClearance.bound ≤ preparedUpper)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (variationMargin : (1 : Coordinate) / 64 ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (ownerAmbientRefines : owner.ambient.Refines box)
    (boxSideBounds : ExactQuadraticOwnerClearance.QuadraticBoxSideMajorantBounds
      (polynomial.eval (segment.pointAt left.parameter)) box 1024)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper (1 / 8 : Coordinate) := by
  have ready : AlreadyPrepared segment left owner request :=
    ⟨boxEq ▸ boxSmall,
      predictedLeEighthFloor.trans eighthFloorLeCurrent,
      boxEq ▸ boxRefines⟩
  let actualCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter))
      owner.track.initial.box directLower preparedUpper := by
    rw [boxEq]
    exact directCache
  have strengthenedCarries :
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound :=
    (variationLtDirectLower.trans_le actualCache.lower_le).trans_le
      (ExactQuadraticOwnerClearance.directBoundaryClearance_le_strengthenQuadraticOwner owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero)
  have canonicalSmall :=
    variation_lt_prepared_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries
  let cached := CachedSource.canonical segment left owner request
  have preparedDominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner :=
    prepared_ambientClearanceDominance_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries dominance
  have preparedBudget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner :=
    prepared_quadraticAmbientBudget_of_ready_of_strengthenedCarries segment
      left owner request ready strengthenedCarries budget
  have preparedAmbientRefines : cached.preparedOwner.ambient.Refines
      owner.ambient := by
    change (prepared segment left owner request).ambient.Refines owner.ambient
    by_cases carries :
        ClearSheetContinuation.variationBound segment
            left.parameter request.endpoint.parameter <
          owner.track.initial.clearance.bound
    · rw [prepared_eq_self_of_ready segment left owner request ready carries]
      exact Box.refines_refl _
    · rw [prepared_eq_strengthenQuadraticOwner_of_ready segment left owner
        request ready carries strengthenedCarries]
      exact ExactQuadraticOwnerClearance.strengthenQuadraticOwner_ambient_refines owner
  have preparedBoxEq : cached.preparedOwner.track.initial.box = box :=
    (prepared_initial_box_eq_of_ready_of_strengthenedCarries segment left
      owner request ready strengthenedCarries).trans boxEq
  have preparedSideBounds : ExactQuadraticOwnerClearance.QuadraticAmbientSideMajorantBounds
      cached.preparedOwner 1024 :=
    ExactQuadraticOwnerClearance.quadraticAmbientSideMajorantBounds_of_box cached.preparedOwner box 1024
      preparedBoxEq (preparedAmbientRefines.trans ownerAmbientRefines)
        boxSideBounds
  have preparedAmbientLeftLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ≤
        preparedUpper := by
    change (prepared segment left owner request).track.initial.ambientLeftClearance.bound ≤
      preparedUpper
    by_cases carries :
        ClearSheetContinuation.variationBound segment
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
      rw [leftEq, ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_eq_max owner
        actualCache.leftNonzero actualCache.rightNonzero
          actualCache.bottomNonzero actualCache.topNonzero]
      exact Fraction.Order.Basic.max_le (dominance.left.trans ownerAmbientLeftLe)
        actualCache.le_upper
  have preparedMargin : (1 : Coordinate) / 64 ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)) :=
    prepared_margin_lower_of_ready_of_strengthenedCarries segment left owner
      request ready strengthenedCarries (1 / 64 : Coordinate) _
        variationMargin
  have advanceCache : ParametricQuadraticAdvanceCache segment within left owner
      request cached canonicalSmall (1 / 8 : Coordinate) := by
    apply eighthFloorQuadraticAdvanceCache_of_sixtyFourthMargin segment
      within left owner request cached canonicalSmall different
        predictedLeEighthFloor preparedDominance preparedMargin
          preparedSideBounds preparedBudget targetNormSqLe
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
    Fraction.Order.Arithmetic.pow_le_pow_direct
      cached.preparedOwner.track.initial.ambientLeftClearance.positive.le
        preparedAmbientLeftLe 2
  have quarterSquareLe :
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4 ≤
        preparedUpper ^ 2 / 4 := by
    change
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 *
          (4 : Coordinate)⁻¹ ≤
        preparedUpper ^ 2 * (4 : Coordinate)⁻¹
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      preparedSquareLe
        (Fraction.Order.Field.inv_pos_direct (by decide)).le
  have nextAmbientLeftLeQuarter :=
    advanceCache.ambientLeftQuarterSq.trans quarterSquareLe
  have nextAmbientRefines :
      (advanceCached segment within left owner request cached
        canonicalSmall).ambient.Refines owner.ambient := by
    rw [advanceCache.ambientBox]
    exact preparedAmbientRefines
  exact ⟨ready, strengthenedCarries, canonicalSmall, preparedAmbientLeftLe,
    advanceCache, nextOwnerBox, nextAmbientLeftLeQuarter,
      nextAmbientRefines⟩

end

section
open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Construct the one-over-128-margin step from the retained same-box state and box-side majorants bounded by 256. -/
public theorem eighthFloorSameBoxStepOfOneTwentyEighthMarginFromState
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box) (preparedUpper : Coordinate)
    (state : ParametricSameBoxState segment left owner box preparedUpper
      (1 / 8 : Coordinate))
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (predictedLeEighthFloor :
      preparedClearanceLower segment left request ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (directLower : Coordinate)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (variationMargin : (1 : Coordinate) / 128 ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (boxSideBounds : ExactQuadraticOwnerClearance.QuadraticBoxSideMajorantBounds
      (polynomial.eval (segment.pointAt left.parameter)) box 256)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper (1 / 8 : Coordinate) :=
  eighthFloorSameBoxStepOfOneTwentyEighthMargin segment within left owner
    request box state.boxEq boxSmall boxRefines predictedLeEighthFloor
      state.clearanceFloor state.dominance state.budget directLower
        preparedUpper state.ambientLeftLe directCache variationLtDirectLower
          different variationMargin state.ambientRefines boxSideBounds
            targetNormSqLe

/-- Construct the three-over-256-margin step from the retained same-box state and box-side majorants bounded by 512. -/
public theorem eighthFloorSameBoxStepOfThreeTwoFiftySixthMarginFromState
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box) (preparedUpper : Coordinate)
    (state : ParametricSameBoxState segment left owner box preparedUpper
      (1 / 8 : Coordinate))
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (predictedLeEighthFloor :
      preparedClearanceLower segment left request ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (directLower : Coordinate)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (variationMargin : (3 : Coordinate) / 256 ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (boxSideBounds : ExactQuadraticOwnerClearance.QuadraticBoxSideMajorantBounds
      (polynomial.eval (segment.pointAt left.parameter)) box 512)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper (1 / 8 : Coordinate) :=
  eighthFloorSameBoxStepOfThreeTwoFiftySixthMargin segment within left owner
    request box state.boxEq boxSmall boxRefines predictedLeEighthFloor
      state.clearanceFloor state.dominance state.budget directLower
        preparedUpper state.ambientLeftLe directCache variationLtDirectLower
          different variationMargin state.ambientRefines boxSideBounds
            targetNormSqLe

/-- Construct the one-over-64-margin step from the retained same-box state and box-side majorants bounded by 1024. -/
public theorem eighthFloorSameBoxStepOfSixtyFourthMarginFromState
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest) (box : Box) (preparedUpper : Coordinate)
    (state : ParametricSameBoxState segment left owner box preparedUpper
      (1 / 8 : Coordinate))
    (boxSmall : box.diagonalSq < request.rootDiameter)
    (boxRefines : box.Refines
      (UniformSquareRootPreparation.rootAmbient segment))
    (predictedLeEighthFloor :
      preparedClearanceLower segment left request ≤
        ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt (1 / 8 : Coordinate))
    (directLower : Coordinate)
    (directCache : ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (polynomial.eval (segment.pointAt left.parameter)) box directLower
        preparedUpper)
    (variationLtDirectLower :
      ClearSheetContinuation.variationBound segment left.parameter
        request.endpoint.parameter < directLower)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (variationMargin : (1 : Coordinate) / 64 ≤
      ClearSheetContinuation.variationBound segment left.parameter
          request.endpoint.parameter -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (boxSideBounds : ExactQuadraticOwnerClearance.QuadraticBoxSideMajorantBounds
      (polynomial.eval (segment.pointAt left.parameter)) box 1024)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    ParametricSameBoxStep segment within left owner request box directLower
      preparedUpper (1 / 8 : Coordinate) :=
  eighthFloorSameBoxStepOfSixtyFourthMargin segment within left owner
    request box state.boxEq boxSmall boxRefines predictedLeEighthFloor
      state.clearanceFloor state.dominance state.budget directLower
        preparedUpper state.ambientLeftLe directCache variationLtDirectLower
          different variationMargin state.ambientRefines boxSideBounds
            targetNormSqLe

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Box identities and fixed quadratic clearance bounds for the actual cached advancement.

The certificate retains ambient dominance, the quadratic budget, and separate quarter-square bounds for the left ambient
clearance and the overall clearance. -/
public structure QuadraticAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound) : Prop where
  /-- The actual advanced initial box equals the retained prepared source box. -/ initialBox :
    (advanceCached segment within left owner request cached
      cachedSmall).track.initial.box = cached.preparedOwner.track.initial.box
  /-- The actual advanced ambient box equals the retained prepared source ambient box. -/ ambientBox :
    (advanceCached segment within left owner request cached
      cachedSmall).ambient = cached.preparedOwner.ambient
  /-- The specified quadratic transport floor is no greater than the indexed owner's clearance. -/ clearanceFloor :
    ExactQuadraticOwnerClearance.quadraticAmbientTransportFloor ≤
    (advanceCached segment within left owner request cached
      cachedSmall).track.initial.clearance.bound
  /-- The advanced left ambient clearance is at most one quarter of the squared source left clearance. -/
    ambientLeftQuarterSq :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.ambientLeftClearance.bound ≤
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  /-- The advanced overall clearance is at most one quarter of the squared source left clearance. -/ clearanceQuarterSq
    :
    (advanceCached segment within left owner request cached
        cachedSmall).track.initial.clearance.bound ≤
      cached.preparedOwner.track.initial.ambientLeftClearance.bound ^ 2 / 4
  /-- The indexed owner's clearance is dominated by each of its retained ambient clearances. -/ dominance :
    ExactQuadraticOwnerClearance.AmbientClearanceDominance
    (advanceCached segment within left owner request cached cachedSmall)
  /-- The indexed owner retains the certified quadratic ambient budget. -/ budget :
    ExactQuadraticOwnerClearance.QuadraticAmbientBudget
    (advanceCached segment within left owner request cached cachedSmall)

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Certify cached advancement with the fixed quadratic floor from a residual margin of at least one half.

Retain distinct endpoint values, ambient dominance, the quadratic budget, a derivative margin at most one quarter, and
target squared norm at most 256. -/
public theorem quadraticAdvanceCache
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (cached : CachedSource segment left owner request)
    (cachedSmall : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        cached.preparedOwner.track.initial.clearance.bound)
    (different :
      polynomial.eval (segment.pointAt left.parameter) ≠
        polynomial.eval (segment.pointAt request.endpoint.parameter))
    (derivativeMarginLe :
      ClearSheetContinuation.squareRootDerivativeMargin segment ≤
        (1 / 4 : Coordinate))
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance cached.preparedOwner)
    (marginLower : (1 : Coordinate) / 2 ≤
      cached.preparedOwner.track.initial.clearance.bound -
        Data.Gaussian.Norm.Basic.normSq
          (polynomial.eval (segment.pointAt left.parameter) -
            polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget cached.preparedOwner)
    (targetNormSqLe : Data.Gaussian.Norm.Basic.normSq
      (polynomial.eval (segment.pointAt request.endpoint.parameter)) ≤ 256) :
    QuadraticAdvanceCache segment within left owner request cached
      cachedSmall := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    request.endpoint.parameter request.endpoint.inside
  let moveSmall :=
    (ClearSheetContinuation.evaluation_variation_le segment
      within left.parameter request.endpoint.parameter left.inside
        request.endpoint.inside).trans_lt cachedSmall
  let transportCache :=
    ExactQuadraticOwnerClearance.quadraticAmbientTransportCache
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

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Recondition the exact transported owner through its retained square-root bridge at the target endpoint. -/
@[expose] public def stepBridge {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (small : ClearSheetContinuation.variationBound segment
      left.parameter request.endpoint.parameter <
        (prepared segment left owner request).track.initial.clearance.bound) :
    SquareRootReconditioning.Bridge
      (segment.pointAt_eval_ne_zero request.endpoint.parameter
        request.endpoint.inside)
      (transported segment within left owner request small) :=
  SquareRootReconditioning.bridge
    (segment.pointAt_eval_ne_zero request.endpoint.parameter
      request.endpoint.inside)
    (transported segment within left owner request small)

open Purelib.Approximation.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Preparation preserves the named square root of the original source owner through every bounded-retry branch.

The constructive equivalence follows each retained candidate's origin and composes its actual common-track or
recentering comparison. -/
@[expose] public def sourceRootEquivalent {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
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
    let common := UniformSquareRootPreparation.bridgeTrack segment
      left.parameter left.inside candidate request.rootDiameter
        request.rootDiameterPositive
    have oldToCommon :=
      SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
        (segment.pointAt_eval_ne_zero left.parameter left.inside) candidate.track
          common
        (UniformSquareRootPreparation.bridgeTrack_initial_strict_owner
          segment left.parameter left.inside candidate
            request.rootDiameterPositive)
    by_cases ready : AlreadyPrepared segment left candidate request
    · have preparedToCommon :=
        SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
          (segment.pointAt_eval_ne_zero left.parameter left.inside)
          (baselinePrepared segment left candidate request).track common (by
            unfold baselinePrepared
            rw [if_pos ready]
            by_cases carries :
                ClearSheetContinuation.variationBound segment
                    left.parameter request.endpoint.parameter <
                  candidate.track.initial.clearance.bound
            · rw [if_pos carries]
              exact
                UniformSquareRootPreparation.bridgeTrack_initial_strict_owner
                  segment left.parameter left.inside candidate request.rootDiameterPositive
            · rw [if_neg carries, ExactQuadraticOwnerClearance.strengthenQuadraticOwner_initial_box]
              exact
                UniformSquareRootPreparation.bridgeTrack_initial_strict_owner
                  segment left.parameter left.inside candidate request.rootDiameterPositive)
      exact Equivalence.NamedEquivalent.trans oldToCommon
        preparedToCommon.symm
    · cases found : (CheckedSquareRootPreparation.attempt segment left.parameter
          candidate request.rootDiameter).value with
      | some accepted =>
          have selected : baselinePrepared segment left candidate request = accepted.value := by
            unfold baselinePrepared
            rw [if_neg ready, found]
          rw [selected]
          exact SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
            (segment.pointAt_eval_ne_zero left.parameter left.inside)
            candidate.track accepted.value.track accepted.strict
      | none =>
          unfold baselinePrepared
          rw [if_neg ready, found]
          exact uniformPreparedRootEquivalent segment left candidate request
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
        simp only [preparedWithRetries, Thunk.get]
        split
        · exact baselineEquivalent candidate
        · exact uniformPreparedRootEquivalent segment left candidate request
    | succ retries inductionHypothesis =>
        intro candidate
        simp only [preparedWithRetries, Thunk.get]
        by_cases carries :
            ClearSheetContinuation.variationBound segment
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
                [SquareRootTrackEquivalence.ownerRootName] using
              recenteredRootEquivalent candidate
          have fallback := Equivalence.NamedEquivalent.trans reset
            (inductionHypothesis (recentered candidate))
          split
          · split
            · exact uniformPreparedRootEquivalent segment left candidate request
            · exact fallback
          · cases coefficientRetry? segment left candidate request (recentered candidate) with
            | none => exact fallback
            | some coefficient =>
                dsimp only
                cases coefficient.origin with
                | coefficient equal =>
                    rw [equal]
                    exact coefficientStrengtheningRootEquivalent candidate
                | movedCoefficient equal =>
                    rw [equal]
                    exact Equivalence.NamedEquivalent.trans reset
                      (coefficientStrengtheningRootEquivalent (recentered candidate))
                | movedBaseline equal =>
                    rw [equal]
                    exact Equivalence.NamedEquivalent.trans reset
                      (baselineEquivalent (recentered candidate))
                | secondReset equal =>
                    rw [equal]
                    exact Equivalence.NamedEquivalent.trans reset
                      (recenteredRootEquivalent (recentered candidate))
  unfold prepared
  exact retryEquivalent preparationRetryCount owner

/-! ## Congruent continuation from equivalent prepared occurrences -/

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Seven strict variation bounds needed to compare continuation of two original root owners.

The bounds separately retain both source clearances, both fresh-owner clearances, both bridge-tail clearances, and the
first owner's fresh common clearance. -/
public structure VariationCongruenceSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left right : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))) : Prop where
  /-- The variation fits the first original owner's clearance. -/ firstSmall : ClearSheetContinuation.variationBound
    segment
    left.parameter right.parameter < first.track.initial.clearance.bound
  /-- The variation fits the second original owner's clearance. -/ secondSmall : ClearSheetContinuation.variationBound
    segment
    left.parameter right.parameter < second.track.initial.clearance.bound
  /-- The variation fits the first owner's retained fresh-source clearance. -/ firstFresh :
    ClearSheetContinuation.variationBound segment
    left.parameter right.parameter <
      SquareRootTrackEquivalence.freshSourceClearance
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first
  /-- The variation fits the second owner's retained fresh-source clearance. -/ secondFresh :
    ClearSheetContinuation.variationBound segment
    left.parameter right.parameter <
      SquareRootTrackEquivalence.freshSourceClearance
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second
  /-- The variation fits the first owner's retained bridge-tail clearance. -/ firstBridge :
    ClearSheetContinuation.variationBound segment
    left.parameter right.parameter <
      SquareRootTrackEquivalence.bridgeTailClearance
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first
  /-- The variation fits the second owner's retained bridge-tail clearance. -/ secondBridge :
    ClearSheetContinuation.variationBound segment
    left.parameter right.parameter <
      SquareRootTrackEquivalence.bridgeTailClearance
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second
  /-- The variation fits the first owner's retained fresh-common clearance. -/ freshCommon :
    ClearSheetContinuation.variationBound segment
    left.parameter right.parameter <
      SquareRootTrackEquivalence.freshCommonClearance
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first

namespace VariationCongruenceSmall

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Turn the seven variation bounds into the corresponding squared-displacement continuation bounds using ambient
containment. -/
public theorem toContinuationCongruenceSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    (within : segment.WithinAmbient)
    {left right : Endpoint}
    {first second : Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (small : VariationCongruenceSmall segment left right first second) :
    SquareRootTrackEquivalence.ContinuationCongruenceSmall
      (segment.pointAt_eval_ne_zero left.parameter left.inside) first second
      (polynomial.eval (segment.pointAt right.parameter)) := by
  have variation :=
    ClearSheetContinuation.evaluation_variation_le segment within
      left.parameter right.parameter left.inside right.inside
  exact
    { firstSmall := (by simpa only [Norm.Basic.normSq_eq_canonical] using (variation.trans_lt small.firstSmall))
      secondSmall := (by simpa only [Norm.Basic.normSq_eq_canonical] using (variation.trans_lt small.secondSmall))
      firstFresh := (by simpa only [Norm.Basic.normSq_eq_canonical] using (variation.trans_lt small.firstFresh))
      secondFresh := (by simpa only [Norm.Basic.normSq_eq_canonical] using (variation.trans_lt small.secondFresh))
      firstBridge := (by simpa only [Norm.Basic.normSq_eq_canonical] using (variation.trans_lt small.firstBridge))
      secondBridge := (by simpa only [Norm.Basic.normSq_eq_canonical] using (variation.trans_lt small.secondBridge))
      freshCommon := (by simpa only [Norm.Basic.normSq_eq_canonical] using (variation.trans_lt small.freshCommon)) }

end VariationCongruenceSmall

open Purelib.Approximation.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Equivalent source roots remain equivalent after separate preparations and continuation to a common target.

Both original owners and requests are retained; the seven variation bounds refer to their actual prepared owners at that
target. -/
@[expose] public def preparedContinuationAtRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (firstRequest secondRequest : StepRequest)
    (target : Endpoint)
    (sourceEquivalent : NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first)
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second))
    (small : VariationCongruenceSmall segment left target
      (prepared segment left first firstRequest)
      (prepared segment left second secondRequest)) :
    NamedEquivalent
      (SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero target.parameter target.inside)
        (prepared segment left first firstRequest)
        (small.toContinuationCongruenceSmall within).firstSmall)
      (SquareRootTrackEquivalence.continuedRootName
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
      (SquareRootTrackEquivalence.ownerRootName sourceNonzero
        firstPrepared)
      (SquareRootTrackEquivalence.ownerRootName sourceNonzero
        secondPrepared) := by
    exact Equivalence.NamedEquivalent.trans
      firstPreparation.symm
        (Equivalence.NamedEquivalent.trans sourceEquivalent
          secondPreparation)
  exact
    SquareRootTrackEquivalence.rootEquivalent_continued_of_rootEquivalent
      sourceNonzero
      (segment.pointAt_eval_ne_zero target.parameter target.inside)
      firstPrepared secondPrepared preparedEquivalent
        (small.toContinuationCongruenceSmall within)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Compare direct continuation with continuation through a prepared intermediate owner representing the same root.

The comparison retains the original source, intermediate owner, source-to-middle and source-to-target moves, and the
exact continuation-congruence bounds. -/
@[expose] public def directToPreparedContinuationRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (left middle target : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (child : Owner
      (polynomial.eval (segment.pointAt middle.parameter)))
    (childRequest : StepRequest)
    (sourceMiddleSmall :
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt left.parameter) -
          polynomial.eval (segment.pointAt middle.parameter)) <
        source.track.initial.clearance.bound)
    (sourceTargetSmall :
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt left.parameter) -
          polynomial.eval (segment.pointAt target.parameter)) <
        source.track.initial.clearance.bound)
    (middleEquivalent : NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
        (source.advance
          (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
          sourceMiddleSmall))
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside) child))
    (congruence :
      SquareRootTrackEquivalence.ContinuationCongruenceSmall
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
        (source.advance
          (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
          sourceMiddleSmall)
        (prepared segment middle child childRequest)
        (polynomial.eval (segment.pointAt target.parameter))) :
    NamedEquivalent
      (SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero target.parameter target.inside)
        source (by simpa only [Norm.Basic.normSq_eq_canonical] using sourceTargetSmall))
      (SquareRootTrackEquivalence.continuedRootName
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
    SquareRootTrackEquivalence.rootEquivalent_continued_compose
      middleNonzero targetNonzero source.track (by simpa only [Norm.Basic.normSq_eq_canonical] using sourceMiddleSmall)
        (by simpa only [Norm.Basic.normSq_eq_canonical] using sourceTargetSmall) congruence.firstSmall
  have childPreparation := sourceRootEquivalent segment middle child
    childRequest
  have middleToPrepared : NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName middleNonzero
        middleOwner)
      (SquareRootTrackEquivalence.ownerRootName middleNonzero
        childPrepared) :=
    Equivalence.NamedEquivalent.trans middleEquivalent
      childPreparation
  have stagedToPrepared :=
    SquareRootTrackEquivalence.rootEquivalent_continued_of_rootEquivalent
      middleNonzero targetNonzero middleOwner childPrepared middleToPrepared
        congruence
  exact Equivalence.NamedEquivalent.trans directToStaged
    stagedToPrepared

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Direct advancement agrees in root name with a prepared, transported, and reserve-retained intermediate step.

The witness composes the supplied intermediate root equivalence with the actual preparation, transport, and retention
comparisons at the requested target. -/
@[expose] public def directToAdvanceRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left middle : Endpoint)
    (source : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (child : Owner
      (polynomial.eval (segment.pointAt middle.parameter)))
    (childRequest : StepRequest)
    (childSmall : ClearSheetContinuation.variationBound segment
      middle.parameter childRequest.endpoint.parameter <
        (prepared segment middle child childRequest).track.initial.clearance.bound)
    (sourceMiddleSmall :
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt left.parameter) -
          polynomial.eval (segment.pointAt middle.parameter)) <
        source.track.initial.clearance.bound)
    (sourceTargetSmall :
      Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt left.parameter) -
          polynomial.eval
            (segment.pointAt childRequest.endpoint.parameter)) <
        source.track.initial.clearance.bound)
    (middleEquivalent : NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
        (source.advance
          (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
          sourceMiddleSmall))
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside) child))
    (congruence :
      SquareRootTrackEquivalence.ContinuationCongruenceSmall
        (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
        (source.advance
          (segment.pointAt_eval_ne_zero middle.parameter middle.inside)
          sourceMiddleSmall)
        (prepared segment middle child childRequest)
        (polynomial.eval
          (segment.pointAt childRequest.endpoint.parameter))) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero childRequest.endpoint.parameter
          childRequest.endpoint.inside)
        (source.advance
          (segment.pointAt_eval_ne_zero childRequest.endpoint.parameter
            childRequest.endpoint.inside)
          sourceTargetSmall))
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero childRequest.endpoint.parameter
          childRequest.endpoint.inside)
        (advance segment within middle child childRequest childSmall)) := by
  let targetNonzero := segment.pointAt_eval_ne_zero
    childRequest.endpoint.parameter childRequest.endpoint.inside
  have directToPrepared := directToPreparedContinuationRootEquivalent segment
    left middle childRequest.endpoint source child childRequest
      sourceMiddleSmall sourceTargetSmall middleEquivalent congruence
  have directToTransported : NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName targetNonzero
        (source.advance targetNonzero sourceTargetSmall))
      (transportedRootName segment within middle child childRequest
        childSmall) := by
    exact Equivalence.NamedEquivalent.trans directToPrepared
      (continuedRootNameEquivalentTransportedRootName segment within middle
        child childRequest childSmall)
  have transportedToAdvance := retainedAtReserveRootEquivalent
    (transported segment within middle child childRequest childSmall)
      (preparedClearanceLower segment middle childRequest)
  simpa only [advance, transportedRootName,
    SquareRootTrackEquivalence.ownerRootName] using
      Equivalence.NamedEquivalent.trans directToTransported
        transportedToAdvance

open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Equivalent source roots yield equivalent prepared continuations for a common request and its certified variation
bounds. -/
@[expose] public def preparedContinuationRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (sourceEquivalent : NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first)
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second))
    (small : VariationCongruenceSmall segment left request.endpoint
      (prepared segment left first request)
      (prepared segment left second request)) :
    NamedEquivalent
      (SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        (prepared segment left first request)
        (small.toContinuationCongruenceSmall within).firstSmall)
      (SquareRootTrackEquivalence.continuedRootName
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        (prepared segment left second request)
        (small.toContinuationCongruenceSmall within).secondSmall) := by
  exact preparedContinuationAtRootEquivalent segment within left first second
    request request request.endpoint sourceEquivalent small

section
open Purelib.Approximation.Gaussian
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation
/-- Equivalent original roots yield equivalent reserved-transport names after their separate preparations for the same
request. -/
@[expose] public def transportedRootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (sourceEquivalent : NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first)
      (SquareRootTrackEquivalence.ownerRootName
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
  exact Equivalence.NamedEquivalent.trans
    firstGenericToTransported.symm
    (Equivalence.NamedEquivalent.trans genericEquivalent
      secondGenericToTransported)

/-- Prepared advancement preserves equivalence of the original source roots under the seven retained variation bounds.
-/
@[expose] public def advanceRootEquivalent_of_rootEquivalent
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Endpoint)
    (first second : Owner
      (polynomial.eval (segment.pointAt left.parameter)))
    (request : StepRequest)
    (sourceEquivalent : NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) first)
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero left.parameter left.inside) second))
    (small : VariationCongruenceSmall segment left request.endpoint
      (prepared segment left first request)
      (prepared segment left second request)) :
    NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (segment.pointAt_eval_ne_zero request.endpoint.parameter
          request.endpoint.inside)
        (advance segment within left first request small.firstSmall))
      (SquareRootTrackEquivalence.ownerRootName
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
    Equivalence.NamedEquivalent.trans firstReset.symm
      (Equivalence.NamedEquivalent.trans transportedEquivalent
        secondReset)
  simpa only [advance, firstTransported, secondTransported, transportedRootName,
    SquareRootTrackEquivalence.ownerRootName] using resetEquivalent

/-! ## Sheet-independent finite mesh checks -/

end

section
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation in
/-- Read the actual prepared clearance of one of the two canonical root owners at the current segment point. -/
@[expose] public def canonicalPreparedClearance {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) (index : Fin 2) :
    Coordinate :=
  (prepared
    segment current
    (SquareRootReconditioning.canonicalOwner
      (segment.pointAt_eval_ne_zero current.parameter current.inside) index)
    request).track.initial.clearance.bound

/-- The minimum of the actual prepared clearances of the two original canonical root owners. -/
@[expose] public def canonicalPreparedClearanceFloor {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) : Coordinate :=
  min
    (canonicalPreparedClearance segment current request
      (⟨0, by decide⟩ : Fin 2))
    (canonicalPreparedClearance segment current request
      (⟨1, by decide⟩ : Fin 2))

open Purelib.Riemann.RootContinuation in
/-- The minimum actual prepared clearance of the two canonical roots is positive. -/
public theorem canonicalPreparedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) :
    0 < canonicalPreparedClearanceFloor segment current request := by
  apply Fraction.Order.Basic.lt_min
  · exact (prepared
      segment current
      (SquareRootReconditioning.canonicalOwner
        (segment.pointAt_eval_ne_zero current.parameter current.inside)
          (⟨0, by decide⟩ : Fin 2)) request).track.initial.clearance.positive
  · exact (prepared
      segment current
      (SquareRootReconditioning.canonicalOwner
        (segment.pointAt_eval_ne_zero current.parameter current.inside)
          (⟨1, by decide⟩ : Fin 2)) request).track.initial.clearance.positive

/-- The minimum actual prepared clearance bounds either retained canonical root's clearance from below. -/
public theorem canonicalPreparedClearanceFloor_le
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) (index : Fin 2) :
    canonicalPreparedClearanceFloor segment current request <=
      canonicalPreparedClearance segment current request index := by
  rcases index with ⟨value, bound⟩
  cases value with
  | zero => exact Fraction.Order.Basic.min_le_left _ _
  | succ value =>
      cases value with
      | zero => exact Fraction.Order.Basic.min_le_right _ _
      | succ value =>
          exact (Nat.not_lt_zero _
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound))).elim

open Purelib.Riemann.RootContinuation in
/-- The canonical prepared-clearance floor bounds preparation of the fresh owner selected from the original root. -/
public theorem canonicalPreparedClearanceFloor_le_freshOwner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    canonicalPreparedClearanceFloor segment current request <=
      (prepared
        segment current
        (SquareRootReconditioning.freshOwner
          (segment.pointAt_eval_ne_zero current.parameter current.inside) owner)
        request).track.initial.clearance.bound := by
  rw [SquareRootReconditioning.freshOwner_eq_canonicalOwner]
  exact canonicalPreparedClearanceFloor_le segment current request _

/-- The predicted preparation clearance, independent of which of the two canonical root indices is supplied. -/
@[expose] public def canonicalPredictedClearance {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) (_index : Fin 2) :
    Coordinate :=
  preparedClearanceLower segment current request

/-- The minimum of the predicted clearances associated with the two canonical root indices. -/
@[expose] public def canonicalPredictedClearanceFloor {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) : Coordinate :=
  min
    (canonicalPredictedClearance segment current request
      (⟨0, by decide⟩ : Fin 2))
    (canonicalPredictedClearance segment current request
      (⟨1, by decide⟩ : Fin 2))

/-- The canonical predicted-clearance floor is strictly positive. -/
public theorem canonicalPredictedClearanceFloor_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) :
    0 < canonicalPredictedClearanceFloor segment current request := by
  apply Fraction.Order.Basic.lt_min <;>
    exact preparedClearanceLower_positive segment current request

/-- The predicted canonical floor is no larger than the minimum actual canonical prepared clearance. -/
public theorem canonicalPredictedClearanceFloor_le_actual
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (request : StepRequest) :
    canonicalPredictedClearanceFloor segment current request ≤
      canonicalPreparedClearanceFloor segment current request := by
  unfold canonicalPredictedClearanceFloor canonicalPreparedClearanceFloor
    canonicalPredictedClearance canonicalPreparedClearance
  exact Fraction.Order.Basic.min_le_min
    (preparedClearanceLower_le segment current _ request)
    (preparedClearanceLower_le segment current _ request)

/-- The predicted canonical floor bounds the prepared clearance of every original owner. -/
public theorem canonicalPredictedClearanceFloor_le_prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    canonicalPredictedClearanceFloor segment current request ≤
      (prepared segment current owner request).track.initial.clearance.bound :=
  (Fraction.Order.Basic.min_le_left _ _).trans
    (preparedClearanceLower_le segment current owner request)

section
open Purelib.Riemann.Branches
/-- Every successive request is ordered and has variation below its owner-independent predicted floor.

The recursive predicate advances through the exact request endpoints, retaining a uniform condition for the remaining
mesh. -/
@[expose] public def FreshMeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    Endpoint -> List StepRequest -> Prop
  | _current, [] => True
  | current, request :: remaining =>
      current.parameter <= request.endpoint.parameter ∧
        ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          canonicalPredictedClearanceFloor segment current request ∧
        FreshMeshSafe segment request.endpoint remaining

/-- The first request fits the actual prepared owner, and all later requests satisfy the uniform predicted-floor
condition.

Each step is ordered by its retained endpoints; the first source owner remains an explicit input to the stronger initial
check. -/
@[expose] public def MeshSafe {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    List StepRequest -> Prop
  | [] => True
  | request :: remaining =>
      current.parameter <= request.endpoint.parameter ∧
        ClearSheetContinuation.variationBound segment
            current.parameter request.endpoint.parameter <
          (prepared segment current owner request).track.initial.clearance.bound ∧
        FreshMeshSafe segment request.endpoint remaining

end

/-- Decide every ordered variation check along the exact finite request list. -/
public instance freshMeshSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint) (requests : List StepRequest) :
    Decidable (FreshMeshSafe segment current requests) := by
  induction requests generalizing current with
  | nil => exact isTrue trivial
  | cons request remaining inductionHypothesis =>
      simp only [FreshMeshSafe]
      letI := inductionHypothesis request.endpoint
      infer_instance

/-- Decide the initial owner-specific check and the remaining uniform mesh checks. -/
public instance meshSafeDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest) :
    Decidable (MeshSafe segment current owner requests) := by
  cases requests with
  | nil => exact isTrue trivial
  | cons request remaining =>
      simp only [MeshSafe]
      infer_instance

end

end Purelib.Riemann.Branches.PreparedSheetContinuation
