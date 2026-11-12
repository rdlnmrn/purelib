module
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Readings.BoundedPreparedSource
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
public import Purelib.RootIsolation.SquareRoot.Replay.BoundedPreparedSourceReplay
public import Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

namespace Purelib.RootIsolation.SquareRoot.Replay.BoundedMovingReplay

open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.Readings
open Purelib.RootIsolation.SquareRoot.Replay
open Purelib.Riemann.Branches.PreparedSheetContinuation

variable {polynomial : GaussianPolynomial} {ambient :
  Box} {start finish : Gaussian}
  (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current :
    Endpoint)
  (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)

/-- Restore the second priority stage, requesting a second reset only after
its ready-owner and same-box tests have failed. -/
def later (inputs : PreparedSourceReplay.Inputs segment request.rootDiameter) (variation :
  Coordinate) :
    MovingRecenterReplay.Plan (Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      (polynomial.eval (segment.pointAt current.parameter)))
      (MovingRecenterReplay.Checked (BoundedPreparedSource.checkLater segment current owner
        request variation)) 5 := by
  let readiness := PreparedSourceReplay.Readiness.capture segment current request owner inputs
  if checkedReady : readiness.Ready then
    have ready := readiness.ready_iff.mp checkedReady
    let strengthened := Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner
    if carries : variation < strengthened.track.initial.clearance.bound then
      let accepted : BoundedPreparedSource.LaterAccepted segment current owner request variation :=
        BoundedPreparedSource.LaterAccepted.strengthened ready strengthened rfl carries
      exact .done ⟨.ok accepted, by
        unfold BoundedPreparedSource.checkLater
        rw [dif_pos ready, dif_pos carries]⟩
    else
      exact (MovingRecenterReplay.moving owner).map fun restored => by
        rcases restored with ⟨restored, equal⟩
        cases restored with
        | none =>
            let failure : BoundedPreparedSource.LaterMiss segment current owner request variation :=
              .exhausted ready strengthened rfl carries (.unavailable equal.symm)
            exact ⟨.error failure, (BoundedPreparedSource.LaterMiss.check_error failure).symm⟩
        | some reset =>
            let resetData := PreparedSourceReplay.Readiness.capture segment current request
              reset.owner inputs
            if checkedReset : resetData.Ready then
              have resetReady := resetData.ready_iff.mp checkedReset
              if resetCarries : variation < reset.owner.track.initial.clearance.bound then
                let accepted : BoundedPreparedSource.LaterAccepted segment current owner request variation :=
                  BoundedPreparedSource.LaterAccepted.moved ready carries reset equal.symm resetReady
                    resetCarries
                refine ⟨.ok accepted, ?_⟩
                unfold BoundedPreparedSource.checkLater
                rw [dif_pos ready, dif_neg carries]
                split
                · rename_i absent
                  cases absent.symm.trans equal.symm
                · rename_i other observed
                  have same := Option.some.inj (observed.symm.trans equal.symm)
                  cases same
                  rw [dif_pos resetReady, dif_pos resetCarries]
              else
                let failure : BoundedPreparedSource.LaterMiss segment current owner request variation :=
                  .exhausted ready strengthened rfl carries (.notCarrying reset equal.symm resetReady resetCarries)
                exact ⟨.error failure, (BoundedPreparedSource.LaterMiss.check_error failure).symm⟩
            else
              have resetReady : ¬ AlreadyPrepared segment current reset.owner
                request :=
                fun ready => checkedReset (resetData.ready_iff.mpr ready)
              let failure : BoundedPreparedSource.LaterMiss segment current owner request variation :=
                .exhausted ready strengthened rfl carries (.notReady reset equal.symm resetReady)
              exact ⟨.error failure, (BoundedPreparedSource.LaterMiss.check_error failure).symm⟩
  else
    have ready : ¬ AlreadyPrepared segment current owner request :=
      fun ready => checkedReady (readiness.ready_iff.mpr ready)
    let failure : BoundedPreparedSource.LaterMiss segment current owner request variation := .notReady ready
    exact .done ⟨.error failure, (BoundedPreparedSource.LaterMiss.check_error failure).symm⟩

/-- Consume the restored later stage. The coefficient cases then use the
original finite helper, which contains no further reset or winding search. -/
def afterMove (inputs : PreparedSourceReplay.Inputs segment request.rootDiameter)
    (ready : AlreadyPrepared segment current owner request)
    (inheritedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < owner.track.initial.clearance.bound)
    (strengthened : Owner (polynomial.eval (segment.pointAt
      current.parameter)))
    (strengthened_eq : strengthened = Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner)
    (directMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < strengthened.track.initial.clearance.bound)
    (moving : BoundedPreparedSource.MoveMiss segment current owner request
      (ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter))
    (moved : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (moved_eq : moved = recentered owner) :
    MovingRecenterReplay.Plan (Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      (polynomial.eval (segment.pointAt current.parameter)))
      (MovingRecenterReplay.Checked (BoundedPreparedSource.afterMoveMiss segment current
        owner request ready inheritedMiss
        (Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner) rfl (by
            rw [← strengthened_eq];
            exact directMiss) moving moved moved_eq)) 5 :=
  (later segment current moved request inputs
    (ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter)).map
      fun restored => by
    let value : BoundedPreparedSourceReplay.Outcome segment current owner request := match
      restored.val with
      | .error later => BoundedPreparedSource.afterLaterMiss segment current owner request ready inheritedMiss
          strengthened strengthened_eq directMiss moving moved moved_eq (moved_eq ▸ later)
      | .ok (BoundedPreparedSource.LaterAccepted.strengthened movedReady value valueEq carries) =>
          .ok
            { cached :=
                { preparedOwner := value
                  preparedOwner_eq := by
                    have movedReady' : AlreadyPrepared segment current
                      (recentered owner) request :=
                      moved_eq ▸ movedReady
                    have movedMiss := fun carrying =>
                      BoundedPreparedSource.MoveMiss.not_carrying moving inheritedMiss ⟨movedReady',
                        carrying⟩
                    have canonical :=
                      prepared_eq_strengthened_recentered_of_ready
                      segment current owner request ready inheritedMiss
                        (by rw [← strengthened_eq]; exact directMiss) movedReady' movedMiss
                        (by rw [← moved_eq, ← valueEq]; exact carries)
                    exact (valueEq.trans (congrArg
                      Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner moved_eq)).trans
                      canonical.symm }
              small := carries }
      | .ok (BoundedPreparedSource.LaterAccepted.moved movedReady strengthenedMiss reset found resetReady
        carries) =>
          .ok
            { cached :=
                { preparedOwner := reset.owner
                  preparedOwner_eq := by
                    have firstReady : AlreadyPrepared segment current
                      (recentered owner) request :=
                      moved_eq ▸ movedReady
                    have firstMiss := fun carrying =>
                      BoundedPreparedSource.MoveMiss.not_carrying moving inheritedMiss ⟨firstReady,
                        carrying⟩
                    have secondEq : recentered
                      (recentered owner) = reset.owner := by
                      rw [← moved_eq]
                      exact recentered_eq_of_movingRecenter_eq_some moved
                        reset found
                    have canonical := prepared_eq_recentered_twice_of_ready
                      segment current owner request ready inheritedMiss
                        (by rw [← strengthened_eq]; exact directMiss) firstReady firstMiss
                        (by rw [← moved_eq]; exact strengthenedMiss)
                        (by rw [secondEq]; exact resetReady) (by rw [secondEq]; exact carries)
                    exact (canonical.trans secondEq).symm }
              small := carries }
    refine ⟨value, ?_⟩
    cases strengthened_eq
    unfold BoundedPreparedSource.afterMoveMiss
    rw [← restored.property]
    rfl

/-- Complete both original moving branches from saved winding replies. The
result certifies the bounded check itself, including every finite miss. -/
def finishMoves (pending : BoundedPreparedSourceReplay.PendingMoves segment current owner request)
    (restored : MovingRecenterReplay.Checked
      (Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner)) :
    MovingRecenterReplay.Plan (Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      (polynomial.eval (segment.pointAt current.parameter)))
      (BoundedPreparedSourceReplay.Checked segment current owner request) 5 := by
  have ready := pending.readiness.ready_iff.mp pending.ready
  have inheritedMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter <
      owner.track.initial.clearance.bound := by
    rw [← pending.movement_eq, ← pending.readiness.clearance_eq]
    exact pending.inheritedMiss
  have directMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter <
      pending.strengthened.track.initial.clearance.bound := by
    rw [← pending.movement_eq]
    exact pending.strengthenedMiss
  have canonicalMiss : ¬ ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter <
      (Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound
        := by
    rw [← pending.strengthened_eq]
    exact directMiss
  rcases restored with ⟨restored, equal⟩
  cases restored with
  | none =>
      have movedEq : owner = recentered owner := by
        unfold recentered; rw [← equal]
      exact (afterMove segment current owner request pending.readiness.inputs
        ready inheritedMiss pending.strengthened
        pending.strengthened_eq directMiss (.unavailable equal.symm) owner movedEq).map fun result =>
        ⟨result.val, by
          unfold BoundedPreparedSource.check
          rw [dif_pos ready, dif_neg inheritedMiss]
          dsimp only
          rw [dif_neg canonicalMiss]
          split
          · exact result.property.symm
          · rename_i reset observed
            cases equal.trans observed⟩
  | some reset =>
      have movedEq : reset.owner = recentered owner :=
        (recentered_eq_of_movingRecenter_eq_some owner reset equal.symm).symm
      let resetData := PreparedSourceReplay.Readiness.capture segment current request reset.owner
        pending.readiness.inputs
      if checkedReset : resetData.Ready then
        have resetReady := resetData.ready_iff.mp checkedReset
        if resetCarries : ClearSheetContinuation.variationBound segment current.parameter
          request.endpoint.parameter <
            reset.owner.track.initial.clearance.bound then
          let accepted := BoundedPreparedSource.acceptedMove segment current owner request ready inheritedMiss
            canonicalMiss
            reset equal.symm resetReady resetCarries
          exact .done ⟨.ok accepted, by
            unfold BoundedPreparedSource.check
            rw [dif_pos ready, dif_neg inheritedMiss]
            dsimp only
            rw [dif_neg canonicalMiss]
            split
            · rename_i absent
              cases equal.trans absent
            · rename_i other observed
              have same := Option.some.inj (observed.symm.trans equal.symm)
              cases same
              rw [dif_pos resetReady, dif_pos resetCarries]⟩
        else
          exact (afterMove segment current owner request pending.readiness.inputs
            ready inheritedMiss pending.strengthened
            pending.strengthened_eq directMiss (.notCarrying reset equal.symm resetReady resetCarries)
            reset.owner movedEq).map fun result =>
            ⟨result.val, by
              unfold BoundedPreparedSource.check
              rw [dif_pos ready, dif_neg inheritedMiss]
              dsimp only
              rw [dif_neg canonicalMiss]
              split
              · rename_i absent
                cases equal.trans absent
              · rename_i other observed
                have same := Option.some.inj (observed.symm.trans equal.symm)
                cases same
                rw [dif_pos resetReady, dif_neg resetCarries]
                exact result.property.symm⟩
      else
        have resetReady : ¬ AlreadyPrepared segment current reset.owner
          request :=
          fun ready => checkedReset (resetData.ready_iff.mpr ready)
        exact (afterMove segment current owner request pending.readiness.inputs
          ready inheritedMiss pending.strengthened
          pending.strengthened_eq directMiss (.notReady reset equal.symm resetReady)
          reset.owner movedEq).map fun result =>
          ⟨result.val, by
            unfold BoundedPreparedSource.check
            rw [dif_pos ready, dif_neg inheritedMiss]
            dsimp only
            rw [dif_neg canonicalMiss]
            split
            · rename_i absent
              cases equal.trans absent
            · rename_i other observed
              have same := Option.some.inj (observed.symm.trans equal.symm)
              cases same
              rw [dif_neg resetReady]
              exact result.property.symm⟩

end Purelib.RootIsolation.SquareRoot.Replay.BoundedMovingReplay
