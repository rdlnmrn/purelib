module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
public import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation.Uniqueness
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic

@[expose] public section

/-!
# Bounded preparation before mesh refinement

Share the inexpensive inherited / same-box strengthening / checked Newton
branches between initial bank selection and direct numerical refinements.
An accepted source retains its exact canonical preparation equation.  A miss
retains the actual input, variation, attempted owner where one was returned,
and the failed comparison or the exact absence of a checked proposal.  The
latter certifies only that the existing finite proposal procedure returned no
owner; it does not identify an invalid curve or assert that every candidate
fails.  A ready owner whose inherited and strengthened bounds miss may use
two checked moving resets, then sharper coefficient certificates on the
original owner and the retained first replacement, in that priority order.
No recursive reset loop or uniform preparation is evaluated by this checker.

The sole import is the existing finite continuation and its preparation
equations.  No new algebraic or analytic assumption is used.
-/

namespace Purelib.Riemann.Readings.BoundedPreparedSource

open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.RootContinuation

open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance (strengthenQuadraticOwner)

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- The actual cached prepared owner with clearance sufficient for the original requested step.

The cache retains its equality to canonical preparation, and the bound pays the variation between the original current
and requested endpoint parameters. -/
structure Accepted {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) where
  /-- The actual prepared-owner cache with its canonical preparation equality. -/ cached : CachedSource segment current
    owner request
  /-- The requested segment variation is strictly below the cached owner's retained clearance. -/ small :
    ClearSheetContinuation.variationBound segment
    current.parameter request.endpoint.parameter < cached.preparedOwner.track.initial.clearance.bound

constructive_injectivity Accepted

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
set_option genInjectivity false in
/-- The exact unsuccessful outcome of one bounded moving-recenter attempt.

The report distinguishes an unavailable candidate, an unprepared candidate and insufficient candidate clearance,
retaining the actual search result and failed condition. -/
inductive MoveMiss {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (variation : Coordinate) : Type where
  /-- The original moving-recenter search returned no candidate. -/ | unavailable
      (found : ExactQuadraticOwnerClearance.movingRecenter? owner = none)
  /-- The tested original or returned candidate owner does not meet the requested preparation condition. -/ | notReady
      (candidate : ExactQuadraticOwnerClearance.MovingRecenter _ owner)
      (found : ExactQuadraticOwnerClearance.movingRecenter? owner = some candidate)
      (unresolved : ¬ AlreadyPrepared segment current candidate.owner request)
  /-- Retain the actual prepared candidate and its failed variation-versus-clearance inequality. -/ | notCarrying
      (candidate : ExactQuadraticOwnerClearance.MovingRecenter _ owner)
      (found : ExactQuadraticOwnerClearance.movingRecenter? owner = some candidate)
      (ready : AlreadyPrepared segment current candidate.owner request)
      (unresolved : ¬ variation < candidate.owner.track.initial.clearance.bound)

constructive_injectivity MoveMiss

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
set_option genInjectivity false in
/-- The unresolved result of checking preparation, strengthening and one subsequent moving recenter.

The exhausted case retains the strengthened owner and its defining equation, failed clearance and the exact
moving-attempt report. -/
inductive LaterMiss {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (variation : Coordinate) : Type where
  /-- The tested original or returned candidate owner does not meet the requested preparation condition. -/ | notReady
    (unresolved : ¬ AlreadyPrepared segment current owner request)
  /-- Retain the exact strengthened candidate, its failed bound and the subsequent moving-attempt miss. -/ | exhausted
      (ready : AlreadyPrepared segment current owner request)
      (strengthened : Owner (polynomial.eval (segment.pointAt current.parameter)))
      (strengthened_eq : strengthened = ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner)
      (unresolved : ¬ variation < strengthened.track.initial.clearance.bound)
      (moving : MoveMiss segment current owner request variation)

constructive_injectivity LaterMiss

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
set_option genInjectivity false in
/-- A retained strengthened or recentered owner that satisfies the original preparation and variation tests.

Each alternative records the actual owner-producing operation and the conditions that led to that branch. -/
inductive LaterAccepted {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (variation : Coordinate) : Type where
  /-- Retain readiness, the actual strengthened owner and its defining equality, and the successful variation bound. -/
    | strengthened
      (ready : AlreadyPrepared segment current owner request)
      (value : Owner (polynomial.eval (segment.pointAt current.parameter)))
      (value_eq : value = ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner)
      (carries : variation < value.track.initial.clearance.bound)
  /-- Retain the failed strengthening bound and the actual successful moving candidate, its search equation, readiness
    and clearance. -/ | moved
      (ready : AlreadyPrepared segment current owner request)
      (strengthenedMiss : ¬ variation <
        (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound)
      (reset : ExactQuadraticOwnerClearance.MovingRecenter _ owner)
      (found : ExactQuadraticOwnerClearance.movingRecenter? owner = some reset)
      (resetReady : AlreadyPrepared segment current reset.owner request)
      (carries : variation < reset.owner.track.initial.clearance.bound)

constructive_injectivity LaterAccepted

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
set_option genInjectivity false in
/-- An unresolved readiness or coefficient-clearance test at the supplied owner.

A clearance miss retains the actual strengthened owner, its defining equation and the failed bound. -/
inductive MovedCoefficientMiss {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (variation : Coordinate) : Type where
  /-- The tested original or returned candidate owner does not meet the requested preparation condition. -/ | notReady
    (unresolved : ¬ AlreadyPrepared segment current owner request)
  /-- Retain the actual prepared candidate and its failed variation-versus-clearance inequality. -/ | notCarrying (ready
    : AlreadyPrepared segment current owner request)
      (value : Owner (polynomial.eval (segment.pointAt current.parameter)))
      (value_eq : value = QuadraticCoefficientClearance.strengthen owner)
      (unresolved : ¬ variation < value.track.initial.clearance.bound)

constructive_injectivity MovedCoefficientMiss

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
set_option genInjectivity false in
/-- The actual coefficient-strengthened owner with preparation and variation evidence.

Its defining equality binds the retained owner to the original strengthening operation at the supplied radicand. -/
structure MovedCoefficientAccepted {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (variation : Coordinate) where
  /-- The original tested owner meets the requested preparation condition. -/ ready : AlreadyPrepared segment current
    owner request
  /-- The actual coefficient-strengthened owner at the original radicand. -/ value : Owner (polynomial.eval
    (segment.pointAt current.parameter))
  /-- The retained value is exactly the coefficient-strengthening result of the supplied owner. -/ value_eq : value =
    QuadraticCoefficientClearance.strengthen owner
  /-- The supplied variation is strictly below the retained owner's clearance. -/ carries : variation <
    value.track.initial.clearance.bound

constructive_injectivity MovedCoefficientAccepted

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Check preparation and the actual coefficient-strengthened owner's clearance.

Success retains the tested owner and bound. An unresolved result identifies the failed readiness or clearance test with
its actual candidate data. -/
def movedCoefficientAttempt {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (variation : Coordinate) :
    Except (MovedCoefficientMiss segment current owner request variation)
      (MovedCoefficientAccepted segment current owner request variation) :=
  if ready : AlreadyPrepared segment current owner request then
    let value := QuadraticCoefficientClearance.strengthen owner
    if carries : variation < value.track.initial.clearance.bound then
      .ok ⟨ready, value, rfl, carries⟩
    else .error (.notCarrying ready value rfl carries)
  else .error (.notReady ready)

open Purelib.Polynomial in
/-- The retained report is exactly the error returned by `movedCoefficientAttempt` at its original inputs.

The candidate equations and failed tests reconstruct the actual branch, preserving the full report rather than only its
error status. -/
private theorem MovedCoefficientMiss.check_error
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : Coordinate}
    (failure : MovedCoefficientMiss segment current owner request variation) :
    movedCoefficientAttempt segment current owner request variation = .error failure := by
  cases failure with
  | notReady unresolved => rw [movedCoefficientAttempt, dif_neg unresolved]
  | notCarrying ready value equal unresolved =>
      cases equal
      rw [movedCoefficientAttempt, dif_pos ready, dif_neg unresolved]

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
set_option genInjectivity false in
/-- The exact unresolved branch of the bounded prepared-source procedure.

The alternatives retain all attempted strengthening and recentering results, or the checked proposal's unavailable or
insufficient outcome, together with the failed inequalities. -/
inductive Miss {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (variation : Coordinate) : Type where
  /-- Retain the failed inherited, strengthened and coefficient bounds, together with both moving-stage and
    moved-coefficient reports. -/ | strengthened
      (ready : AlreadyPrepared segment current owner request)
      (inheritedMiss : ¬ variation < owner.track.initial.clearance.bound)
      (candidate : Owner (polynomial.eval (segment.pointAt current.parameter)))
      (candidate_eq : candidate = ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner)
      (candidateMiss : ¬ variation < candidate.track.initial.clearance.bound)
      (coefficient : Owner (polynomial.eval (segment.pointAt current.parameter)))
      (coefficient_eq : coefficient = QuadraticCoefficientClearance.strengthen owner)
      (coefficientMiss : ¬ variation < coefficient.track.initial.clearance.bound)
      (moving : MoveMiss segment current owner request variation)
      (later : LaterMiss segment current (recentered owner) request variation)
      (movedCoefficient : MovedCoefficientMiss segment current (recentered owner) request variation)
  /-- Retain failed preparation, its exact unavailable equation and the actual first failed search or guard. -/
  | proposalUnavailable
      (notReady : ¬ AlreadyPrepared segment current owner request)
      (unavailable : (CheckedSquareRootPreparation.attempt segment current.parameter
        owner request.rootDiameter).value = none)
      (diagnostic : CheckedSquareRootPreparation.Failure segment current.parameter owner request.rootDiameter)
  /-- Retain the actual checked proposal, its successful search equation and its insufficient clearance bound. -/ |
    proposalMiss
      (notReady : ¬ AlreadyPrepared segment current owner request)
      (candidate : CheckedSquareRootPreparation.Result segment current.parameter
        owner request.rootDiameter)
      (candidate_eq : (CheckedSquareRootPreparation.attempt segment current.parameter
        owner request.rootDiameter).value = some candidate)
      (candidateMiss : ¬ variation < candidate.value.track.initial.clearance.bound)

constructive_injectivity Miss

open Purelib.Polynomial in
set_option genInjectivity false in
/-- An unresolved bounded preparation attempt tied to its original source, endpoint and request.

The report retains the exact variation bound, the two-step moving budget and the branch-specific unresolved evidence. It
makes no claim that another preparation attempt cannot succeed. -/
structure Inconclusive {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) where
  /-- The original source owner retained by the inconclusive report. -/ source : Owner (polynomial.eval (segment.pointAt
    current.parameter))
  /-- The retained source is exactly the original input owner. -/ source_eq : source = owner
  /-- The original current endpoint retained by the report. -/ endpoint : Endpoint
  /-- The retained endpoint is exactly the input current endpoint. -/ endpoint_eq : endpoint = current
  /-- The original continuation request retained by the report. -/ requested : StepRequest
  /-- The retained request is exactly the input request. -/ requested_eq : requested = request
  /-- The actual segment variation tested by the procedure. -/ variation : Coordinate
  /-- The retained variation equals the original current-to-requested-endpoint variation bound. -/ variation_eq :
    variation = ClearSheetContinuation.variationBound segment
    current.parameter request.endpoint.parameter
  /-- The retained finite moving-recenter budget. -/ movingBudget : Nat
  /-- The original procedure's moving-recenter budget is exactly two. -/ movingBudget_eq : movingBudget = 2
  /-- The exact unresolved branch bound to the retained original source, request and variation. -/ reason : Miss segment
    current source requested variation

constructive_injectivity Inconclusive

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Package the actual successful moving-recenter candidate as the original request's cached prepared owner.

The earlier failed bounds and returned candidate equation identify this exact owner with canonical preparation; its
retained clearance pays the requested variation. -/
def acceptedMove {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (inheritedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < owner.track.initial.clearance.bound)
    (strengthenedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < (ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound)
    (reset : ExactQuadraticOwnerClearance.MovingRecenter _ owner)
    (found : ExactQuadraticOwnerClearance.movingRecenter? owner = some reset)
    (resetReady : AlreadyPrepared segment current reset.owner request)
    (carries : ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < reset.owner.track.initial.clearance.bound) :
    Accepted segment current owner request where
  cached :=
    { preparedOwner := reset.owner
      preparedOwner_eq := by
        have resetEq := recentered_eq_of_movingRecenter_eq_some owner reset found
        have canonical := prepared_eq_recentered_of_ready segment current owner request
          ready inheritedMiss strengthenedMiss
          (by rw [resetEq]; exact resetReady) (by rw [resetEq]; exact carries)
        exact (canonical.trans resetEq).symm }
  small := carries

open Purelib.Polynomial in
/-- A moving-attempt miss and insufficient inherited clearance exclude readiness together with sufficient recentered
clearance. -/
public theorem MoveMiss.not_carrying
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : Coordinate}
    (report : MoveMiss segment current owner request variation)
    (inheritedMiss : ¬ variation < owner.track.initial.clearance.bound) :
    ¬ (AlreadyPrepared segment current (recentered owner) request ∧
      variation < (recentered owner).track.initial.clearance.bound) := by
  intro bounds
  cases report with
  | unavailable found =>
      have unchanged : recentered owner = owner := by
        unfold recentered
        rw [found]
      rw [unchanged] at bounds
      exact inheritedMiss bounds.2
  | notReady candidate found unresolved =>
      rw [recentered_eq_of_movingRecenter_eq_some owner candidate found] at bounds
      exact unresolved bounds.1
  | notCarrying candidate found _ unresolved =>
      rw [recentered_eq_of_movingRecenter_eq_some owner candidate found] at bounds
      exact unresolved bounds.2

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Check strengthening and then one actual moving recenter of an already prepared source.

The result retains either the successful owner and its provenance or the precise failed readiness, strengthening and
recentering evidence. -/
def checkLater
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (variation : Coordinate) :
    Except (LaterMiss segment current owner request variation)
      (LaterAccepted segment current owner request variation) :=
  if ready : AlreadyPrepared segment current owner request then
    let strengthened := ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner
    if carries : variation < strengthened.track.initial.clearance.bound then
      .ok (.strengthened ready strengthened rfl carries)
    else
      match found : ExactQuadraticOwnerClearance.movingRecenter? owner with
      | none => .error (.exhausted ready strengthened rfl carries (.unavailable found))
      | some reset =>
          if resetReady : AlreadyPrepared segment current reset.owner request then
            if resetCarries : variation < reset.owner.track.initial.clearance.bound then
              .ok (.moved ready carries reset found resetReady resetCarries)
            else .error (.exhausted ready strengthened rfl carries
              (.notCarrying reset found resetReady resetCarries))
          else .error (.exhausted ready strengthened rfl carries (.notReady reset found resetReady))
  else .error (.notReady ready)

open Purelib.Polynomial in
/-- The retained report is exactly the error returned by `checkLater` at its original inputs.

The candidate equations and failed tests reconstruct the actual branch, preserving the full report rather than only its
error status. -/
public theorem LaterMiss.check_error
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : Coordinate}
    (report : LaterMiss segment current owner request variation) :
    checkLater segment current owner request variation = .error report := by
  cases report with
  | notReady unresolved => rw [checkLater, dif_neg unresolved]
  | exhausted ready strengthened equal unresolved moving =>
      cases equal
      rw [checkLater, dif_pos ready, dif_neg unresolved]
      cases moving with
      | unavailable found =>
          split
          · rfl
          · rename_i reset observed
            have impossible : some reset = none := observed.symm.trans found
            cases impossible
      | notReady reset found unresolved =>
          split
          · rename_i observed
            have impossible : none = some reset := observed.symm.trans found
            cases impossible
          · rename_i other observed
            have equal : other = reset := Option.some.inj (observed.symm.trans found)
            cases equal
            rw [dif_neg unresolved]
      | notCarrying reset found resetReady unresolved =>
          split
          · rename_i observed
            have impossible : none = some reset := observed.symm.trans found
            cases impossible
          · rename_i other observed
            have equal : other = reset := Option.some.inj (observed.symm.trans found)
            cases equal
            rw [dif_pos resetReady, dif_neg unresolved]

section
open Purelib.Polynomial
open Purelib.RootIsolation.SquareRoot.Clearance
/-- A later-attempt miss at a ready source certifies insufficient strengthened clearance. -/
public theorem LaterMiss.strengthened_miss
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : Coordinate}
    (report : LaterMiss segment current owner request variation)
    (ready : AlreadyPrepared segment current owner request) :
    ¬ variation < (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound := by
  cases report with
  | notReady unresolved => exact (unresolved ready).elim
  | exhausted _ _ equal unresolved _ => rw [equal] at unresolved; exact unresolved

/-- A later-attempt miss at a ready source excludes a ready recentered owner with sufficient clearance. -/
public theorem LaterMiss.second_miss
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : Coordinate}
    (report : LaterMiss segment current owner request variation)
    (ready : AlreadyPrepared segment current owner request) :
    ¬ (AlreadyPrepared segment current (recentered owner) request ∧
      variation < (recentered owner).track.initial.clearance.bound) := by
  cases report with
  | notReady unresolved => exact (unresolved ready).elim
  | exhausted _ _ equal unresolved moving =>
      rw [equal] at unresolved
      exact moving.not_carrying (fun small =>
        unresolved (small.trans_le
          (ExactQuadraticOwnerClearance.strengthenQuadraticOwner_clearance_le owner)))

end

section
open Purelib.Polynomial
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Check coefficient strengthening after the retained earlier strengthening and moving attempts failed.

The procedure first checks the original owner's coefficient strengthening, then the moved owner's. Success retains the
exact canonical prepared-owner cache; failure records both candidates and every prior unresolved test. -/
def afterLaterMiss
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (inheritedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < owner.track.initial.clearance.bound)
    (strengthened : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (strengthened_eq : strengthened = ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner)
    (directMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < strengthened.track.initial.clearance.bound)
    (moving : MoveMiss segment current owner request
      (ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter))
    (moved : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (moved_eq : moved = recentered owner)
    (later : LaterMiss segment current (recentered owner) request
      (ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter)) :
    Except (Inconclusive segment current owner request) (Accepted segment current owner request) :=
  let coefficient := QuadraticCoefficientClearance.strengthen owner
  if carries : ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < coefficient.track.initial.clearance.bound then
    .ok
      { cached :=
          { preparedOwner := coefficient
            preparedOwner_eq := (prepared_eq_coefficient_of_ready segment current owner request
              ready inheritedMiss (by rw [← strengthened_eq]; exact directMiss)
              (moving.not_carrying inheritedMiss) later.strengthened_miss later.second_miss
                carries).symm }
        small := carries }
  else
    match movedCoefficientAttempt segment current moved request
        (ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter) with
    | .ok accepted =>
        .ok
          { cached :=
              { preparedOwner := accepted.value
                preparedOwner_eq := by
                  have movedReady : AlreadyPrepared segment current (recentered owner) request :=
                    moved_eq ▸ accepted.ready
                  have canonical := prepared_eq_moved_coefficient_of_ready segment current owner request
                    ready inheritedMiss (by rw [← strengthened_eq]; exact directMiss) movedReady
                    (fun carrying => moving.not_carrying inheritedMiss ⟨movedReady, carrying⟩)
                    (later.strengthened_miss movedReady) (later.second_miss movedReady) carries
                    (by rw [← moved_eq, ← accepted.value_eq]; exact accepted.carries)
                  exact (accepted.value_eq.trans
                    (congrArg QuadraticCoefficientClearance.strengthen moved_eq)).trans canonical.symm }
            small := accepted.carries }
    | .error failure => .error
        { source := owner, source_eq := rfl, endpoint := current, endpoint_eq := rfl
          requested := request, requested_eq := rfl
          variation := ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter
          variation_eq := rfl, movingBudget := 2, movingBudget_eq := rfl
          reason := .strengthened ready inheritedMiss strengthened strengthened_eq directMiss
            coefficient rfl carries moving later (moved_eq ▸ failure) }

/-- Continue the bounded procedure from its actual recentered owner after the first moving attempt misses.

Strengthening or one further recenter can supply the accepted cache. A later miss is passed with its exact evidence to
the remaining coefficient-clearance checks. -/
def afterMoveMiss
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (ready : AlreadyPrepared segment current owner request)
    (inheritedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < owner.track.initial.clearance.bound)
    (strengthened : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (strengthened_eq : strengthened = ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner)
    (directMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < strengthened.track.initial.clearance.bound)
    (moving : MoveMiss segment current owner request
      (ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter))
    (moved : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (moved_eq : moved = recentered owner) :
    Except (Inconclusive segment current owner request) (Accepted segment current owner request) :=
  match checkLater segment current moved request
      (ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter) with
  | .error later => afterLaterMiss segment current owner request ready inheritedMiss
      strengthened strengthened_eq directMiss moving moved moved_eq (moved_eq ▸ later)
  | .ok (.strengthened movedReady value valueEq carries) =>
      .ok
        { cached :=
            { preparedOwner := value
              preparedOwner_eq := by
                have movedReady' : AlreadyPrepared segment current (recentered owner) request :=
                  moved_eq ▸ movedReady
                have movedMiss := fun carrying =>
                  moving.not_carrying inheritedMiss ⟨movedReady', carrying⟩
                have canonical := prepared_eq_strengthened_recentered_of_ready
                  segment current owner request ready inheritedMiss
                    (by rw [← strengthened_eq]; exact directMiss) movedReady' movedMiss
                    (by rw [← moved_eq, ← valueEq]; exact carries)
                exact (valueEq.trans (congrArg ExactQuadraticOwnerClearance.strengthenQuadraticOwner moved_eq)).trans
                  canonical.symm }
          small := carries }
  | .ok (.moved movedReady strengthenedMiss reset found resetReady carries) =>
      .ok
        { cached :=
            { preparedOwner := reset.owner
              preparedOwner_eq := by
                have firstReady : AlreadyPrepared segment current (recentered owner) request :=
                  moved_eq ▸ movedReady
                have firstMiss := fun carrying =>
                  moving.not_carrying inheritedMiss ⟨firstReady, carrying⟩
                have secondEq : recentered (recentered owner) = reset.owner := by
                  rw [← moved_eq]
                  exact recentered_eq_of_movingRecenter_eq_some moved reset found
                have canonical := prepared_eq_recentered_twice_of_ready
                  segment current owner request ready inheritedMiss
                    (by rw [← strengthened_eq]; exact directMiss) firstReady firstMiss
                    (by rw [← moved_eq]; exact strengthenedMiss)
                    (by rw [secondEq]; exact resetReady) (by rw [secondEq]; exact carries)
                exact (canonical.trans secondEq).symm }
          small := carries }

/-- A retained later miss identifies the continuation with the exact coefficient-check fallback branch. -/
private theorem afterMoveMiss_eq_afterLaterMiss
    {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest}
    {ready : AlreadyPrepared segment current owner request}
    {inheritedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < owner.track.initial.clearance.bound}
    {strengthened : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {strengthened_eq : strengthened = ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner}
    {directMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < strengthened.track.initial.clearance.bound}
    {moving : MoveMiss segment current owner request
      (ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter)}
    {moved : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {moved_eq : moved = recentered owner}
    (later : LaterMiss segment current (recentered owner) request
      (ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter)) :
    afterMoveMiss segment current owner request ready inheritedMiss
        strengthened strengthened_eq directMiss moving moved moved_eq =
      afterLaterMiss segment current owner request ready inheritedMiss
        strengthened strengthened_eq directMiss moving (recentered owner) rfl later := by
  cases moved_eq
  rw [afterMoveMiss, later.check_error]

/-- Run the bounded source-preparation procedure and return its exact success or inconclusive certificate.

Ready sources try inherited clearance, strengthening, at most two moving recenter stages and coefficient strengthening.
Unready sources use the checked square-root proposal. Every success retains the owner equal to canonical preparation;
every unsuccessful branch retains its actual inputs, budget and failed conditions. -/
@[irreducible] def check {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) :
    Except (Inconclusive segment current owner request) (Accepted segment current owner request) :=
  let variation := ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter
  let inconclusive : Miss segment current owner request variation →
      Except (Inconclusive segment current owner request) (Accepted segment current owner request) :=
    fun reason => .error
      { source := owner, source_eq := rfl, endpoint := current, endpoint_eq := rfl
        requested := request, requested_eq := rfl, variation := variation, variation_eq := rfl
        movingBudget := 2, movingBudget_eq := rfl
        reason := reason }
  if ready : AlreadyPrepared segment current owner request then
    if small : variation < owner.track.initial.clearance.bound then
      .ok
        { cached := ⟨owner, (prepared_eq_self_of_ready segment current owner request ready small).symm⟩
          small := small }
    else
      let strengthened := ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner
      if carries : variation < strengthened.track.initial.clearance.bound then
        .ok
          { cached := ⟨strengthened,
              (prepared_eq_strengthenQuadraticOwner_of_ready segment current owner request
                ready small carries).symm⟩
            small := carries }
      else
        match moved : ExactQuadraticOwnerClearance.movingRecenter? owner with
        | none => afterMoveMiss segment current owner request ready small strengthened rfl carries
            (.unavailable moved) owner (by unfold recentered; rw [moved])
        | some reset =>
            if resetReady : AlreadyPrepared segment current reset.owner request then
              if resetCarries : variation < reset.owner.track.initial.clearance.bound then
                .ok (acceptedMove segment current owner request ready small carries
                  reset moved resetReady resetCarries)
              else afterMoveMiss segment current owner request ready small strengthened rfl carries
                (.notCarrying reset moved resetReady resetCarries) reset.owner
                (recentered_eq_of_movingRecenter_eq_some owner reset moved).symm
            else afterMoveMiss segment current owner request ready small strengthened rfl carries
              (.notReady reset moved resetReady) reset.owner
              (recentered_eq_of_movingRecenter_eq_some owner reset moved).symm
  else
    let proposal := CheckedSquareRootPreparation.attempt segment current.parameter owner request.rootDiameter
    match found : proposal.value with
    | none => inconclusive (.proposalUnavailable ready found
        (proposal.failure segment current.parameter owner request.rootDiameter found))
    | some accepted =>
        if carries : variation < accepted.value.track.initial.clearance.bound then
          .ok
            { cached := ⟨accepted.value,
                (prepared_eq_checked_of_not_ready segment current owner request ready accepted
                  found carries).symm⟩
              small := carries }
        else inconclusive (.proposalMiss ready accepted found carries)

end

open Purelib.Polynomial
/-- An accepted cache supplies the requested variation bound for the exact canonical prepared owner. -/
theorem Accepted.canonical_small {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} (accepted : Accepted segment current owner request) :
    ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
      (prepared segment current owner request).track.initial.clearance.bound := by
  rw [← accepted.cached.preparedOwner_eq]
  exact accepted.small

/-- The retained report is exactly the error returned by `check` at its original inputs.

The candidate equations and failed tests reconstruct the actual branch, preserving the full report rather than only its
error status. -/
theorem Inconclusive.check_error {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} (report : Inconclusive segment current owner request) :
    check segment current owner request = .error report := by
  cases report with
  | mk source sourceEq endpoint endpointEq requested requestedEq variation variationEq
      movingBudget movingBudgetEq reason =>
      cases sourceEq
      cases endpointEq
      cases requestedEq
      cases variationEq
      cases movingBudgetEq
      cases reason with
      | strengthened ready inheritedMiss candidate candidateEq candidateMiss
          coefficient coefficientEq coefficientMiss moving later movedCoefficient =>
          cases candidateEq
          cases coefficientEq
          unfold check
          rw [dif_pos ready, dif_neg inheritedMiss, dif_neg candidateMiss]
          cases moving with
          | unavailable found =>
              split
              · rw [afterMoveMiss_eq_afterLaterMiss later, afterLaterMiss, dif_neg coefficientMiss,
                  movedCoefficient.check_error]
              · rename_i reset observed
                have impossible : some reset = none := observed.symm.trans found
                cases impossible
          | notReady reset found unresolved =>
              split
              · rename_i observed
                have impossible : none = some reset := observed.symm.trans found
                cases impossible
              · rename_i other observed
                have equal : other = reset := Option.some.inj (observed.symm.trans found)
                cases equal
                rw [dif_neg unresolved, afterMoveMiss_eq_afterLaterMiss later,
                  afterLaterMiss, dif_neg coefficientMiss, movedCoefficient.check_error]
          | notCarrying reset found resetReady unresolved =>
              split
              · rename_i observed
                have impossible : none = some reset := observed.symm.trans found
                cases impossible
              · rename_i other observed
                have equal : other = reset := Option.some.inj (observed.symm.trans found)
                cases equal
                rw [dif_pos resetReady, dif_neg unresolved, afterMoveMiss_eq_afterLaterMiss later,
                  afterLaterMiss, dif_neg coefficientMiss, movedCoefficient.check_error]
      | proposalUnavailable notReady unavailable diagnostic =>
          unfold check
          rw [dif_neg notReady]
          dsimp only
          split
          · rename_i found
            have same := CheckedSquareRootPreparation.Failure.unique segment current.parameter
              owner request.rootDiameter diagnostic
              ((CheckedSquareRootPreparation.attempt segment current.parameter owner request.rootDiameter).failure
                segment current.parameter owner request.rootDiameter found)
            cases same
            rfl
          · rename_i other found
            have impossible : some other = none := found.symm.trans unavailable
            cases impossible
      | proposalMiss notReady candidate candidateEq candidateMiss =>
          unfold check
          rw [dif_neg notReady]
          dsimp only
          split
          · rename_i found
            have impossible : none = some candidate := found.symm.trans candidateEq
            cases impossible
          · rename_i other found
            have equal : other = candidate := Option.some.inj (found.symm.trans candidateEq)
            cases equal
            rw [dif_neg candidateMiss]

end Purelib.Riemann.Readings.BoundedPreparedSource
