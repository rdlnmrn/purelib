module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.Riemann.Readings.BoundedPreparedSource
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
import Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
Replay the bounded source check used by adaptive bank selection.  Unlike a
canonical prepared-owner equation alone, `Checked.equation` identifies the
bounded check's actual outcome; this is needed to retain rejected depths.
Diameter proposals come from the existing exact checkpoint checker.  The
remaining ready-owner moving branches are exposed, never silently replaced
by the original search or misreported as a rejected bank depth.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.BoundedPreparedSourceReplay

open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.Readings
open Purelib.Riemann.RootContinuation Purelib.RootIsolation.SquareRoot.Replay
open Purelib.Riemann.Branches.PreparedSheetContinuation

variable {polynomial : GaussianPolynomial} {ambient :
  Box} {start finish : Gaussian}
  (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current :
    Endpoint)
  (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)

/-- The original bounded preparation's typed accepted or inconclusive result. -/
abbrev Outcome := Except (BoundedPreparedSource.Inconclusive segment current owner request)
  (BoundedPreparedSource.Accepted segment current owner request)

set_option genInjectivity false in
/-- A retained outcome equal to the exact original bounded source-checking procedure. -/
structure Checked where
  /-- The exact retained accepted or inconclusive outcome. -/ value :
    Outcome segment current owner request
  /-- The original bounded source checker returns this retained outcome. -/ equation :
    BoundedPreparedSource.check segment current owner request = value

constructive_injectivity Checked

set_option genInjectivity false in
/-- All comparisons already performed before the first missing moving-reset
checkpoint.  This is an unresolved replay branch, not a bounded-check error. -/
structure PendingMoves where
  /-- The original inherited owner's cached readiness measurements. -/ readiness :
    PreparedSourceReplay.Readiness segment current request owner
  /-- The cached inherited owner passes the original readiness conditions. -/ ready : readiness.Ready
  /-- The original segment variation bound retained for the carrying comparisons. -/ movement :
    Coordinate
  /-- The retained movement equals the original variation-bound computation. -/ movement_eq : movement =
    ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter
  /-- The ready inherited owner does not carry the retained movement. -/ inheritedMiss : ¬ movement <
    readiness.clearance
  /-- The actual same-box strengthened owner. -/ strengthened : Owner
    (polynomial.eval (segment.pointAt current.parameter))
  /-- The retained strengthened owner equals the original strengthening of the inherited owner. -/ strengthened_eq :
    strengthened = Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner
  /-- The original strengthened owner still does not carry the retained movement. -/ strengthenedMiss : ¬ movement <
    strengthened.track.initial.clearance.bound
  /-- The number of moving-reset attempts retained by the original bounded checker. -/ movingBudget : Nat := 2
  /-- The retained moving-reset budget is exactly two. -/ movingBudget_eq : movingBudget = 2 := by rfl

constructive_injectivity PendingMoves

set_option genInjectivity false in
/-- The first checked preparation branch or its retained unresolved replay work.

Ready inherited and strengthened sources may finish immediately; other branches retain either failed diameter readiness
or the pending moving-reset comparisons. -/
inductive Start where
  /-- The original bounded outcome is already identified exactly. -/ | checked (result :
    Checked segment current owner request)
  /-- Retain the inherited readiness measurements and their failed condition for diameter replay. -/ | diameter
    (readiness : PreparedSourceReplay.Readiness segment current request owner) (notReady : ¬
    readiness.Ready)
  /-- Retain the successful readiness and failed carrying comparisons preceding moving-reset replay. -/ | moving
    (pending : PendingMoves segment current owner request)

constructive_injectivity Start

/-- The inherited and same-box cases need no root proposal generation. -/
@[expose] def begin (inputs : PreparedSourceReplay.Inputs segment request.rootDiameter) :
  Start segment current owner request := by
  let readiness := PreparedSourceReplay.Readiness.capture segment current request owner inputs
  if ready : readiness.Ready then
    have originalReady := readiness.ready_iff.mp ready
    let movement := ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter
    if carries : movement < readiness.clearance then
      have small : movement < owner.track.initial.clearance.bound := by
        rw [← readiness.clearance_eq]
        exact carries
      let accepted : BoundedPreparedSource.Accepted segment current owner request :=
        ⟨⟨owner, (prepared_eq_self_of_ready segment current owner request
          originalReady small).symm⟩, small⟩
      exact .checked ⟨.ok accepted, by
        unfold BoundedPreparedSource.check
        rw [dif_pos originalReady, dif_pos small]⟩
    else
      have inheritedMiss : ¬ movement < owner.track.initial.clearance.bound := by
        rw [← readiness.clearance_eq]
        exact carries
      let strengthened := Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner
      if stronger : movement < strengthened.track.initial.clearance.bound then
        let accepted : BoundedPreparedSource.Accepted segment current owner request :=
          ⟨⟨strengthened, (prepared_eq_strengthenQuadraticOwner_of_ready
            segment current owner request
              originalReady inheritedMiss stronger).symm⟩, stronger⟩
        exact .checked ⟨.ok accepted, by
          unfold BoundedPreparedSource.check
          rw [dif_pos originalReady, dif_neg inheritedMiss, dif_pos stronger]⟩
      else
        exact .moving ⟨readiness, ready, movement, rfl, carries, strengthened, rfl, stronger, 2, rfl⟩
  else exact .diameter readiness ready

/-- A restored attempt identifies both success and finite failure of the
original bounded checker.  No remaining source search is executed. -/
@[expose] def finishDiameter (notReady : ¬ AlreadyPrepared segment current
  owner request)
    (attempt : Option (CheckedSquareRootPreparation.Result segment current.parameter owner
      request.rootDiameter))
    (found : (CheckedSquareRootPreparation.attempt segment current.parameter owner
      request.rootDiameter).value = attempt)
    (diagnostic : attempt = none → CheckedSquareRootPreparation.Failure
      segment current.parameter owner request.rootDiameter) :
    Checked segment current owner request := by
  let movement := ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter
  cases attempt with
  | none =>
      let report : BoundedPreparedSource.Inconclusive segment current owner request :=
        ⟨owner, rfl, current, rfl, request, rfl, movement, rfl, 2, rfl,
          .proposalUnavailable notReady found (diagnostic rfl)⟩
      exact ⟨.error report, report.check_error⟩
  | some candidate =>
      if carries : movement < candidate.value.track.initial.clearance.bound then
        let accepted : BoundedPreparedSource.Accepted segment current owner request :=
          ⟨⟨candidate.value, (prepared_eq_checked_of_not_ready segment
            current owner request
              notReady candidate found carries).symm⟩, carries⟩
        exact ⟨.ok accepted, by
          unfold BoundedPreparedSource.check
          rw [dif_neg notReady]
          dsimp only
          split
          · rename_i empty
            cases empty.symm.trans found
          · rename_i other observed
            have same := Option.some.inj (observed.symm.trans found)
            cases same
            rw [dif_pos carries]⟩
      else
        let report : BoundedPreparedSource.Inconclusive segment current owner request :=
          ⟨owner, rfl, current, rfl, request, rfl, movement, rfl, 2, rfl,
            .proposalMiss notReady candidate found carries⟩
        exact ⟨.error report, report.check_error⟩

end Purelib.RootIsolation.SquareRoot.Replay.BoundedPreparedSourceReplay

end
