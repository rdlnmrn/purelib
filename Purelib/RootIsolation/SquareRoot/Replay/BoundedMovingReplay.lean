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

variable {polynomial : Riemann.Branches.PreparedSheetContinuation.GaussianPolynomial} {ambient :
  Riemann.Branches.PreparedSheetContinuation.Box} {start finish : Riemann.Branches.PreparedSheetContinuation.Gaussian}
  (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current :
    Riemann.Branches.PreparedSheetContinuation.Endpoint)
  (owner : Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : Riemann.Branches.PreparedSheetContinuation.StepRequest)

/-- Restore the second priority stage, requesting a second reset only after
its ready-owner and same-box tests have failed. -/
def later (inputs : SquareRoot.Replay.PreparedSourceReplay.Inputs segment request.rootDiameter) (variation :
  Riemann.Branches.PreparedSheetContinuation.Coordinate) :
    SquareRoot.Replay.MovingRecenterReplay.Plan (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      (polynomial.eval (segment.pointAt current.parameter)))
      (SquareRoot.Replay.MovingRecenterReplay.Checked (Readings.BoundedPreparedSource.checkLater segment current owner
        request variation)) 5 := by
  let readiness := SquareRoot.Replay.PreparedSourceReplay.Readiness.capture segment current request owner inputs
  if checkedReady : readiness.Ready then
    have ready := readiness.ready_iff.mp checkedReady
    let strengthened := SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner
    if carries : variation < strengthened.track.initial.clearance.bound then
      let accepted : Readings.BoundedPreparedSource.LaterAccepted segment current owner request variation :=
        Readings.BoundedPreparedSource.LaterAccepted.strengthened ready strengthened rfl carries
      exact .done ⟨.ok accepted, by
        unfold Readings.BoundedPreparedSource.checkLater
        rw [dif_pos ready, dif_pos carries]⟩
    else
      exact (SquareRoot.Replay.MovingRecenterReplay.moving owner).map fun restored => by
        rcases restored with ⟨restored, equal⟩
        cases restored with
        | none =>
            let failure : Readings.BoundedPreparedSource.LaterMiss segment current owner request variation :=
              .exhausted ready strengthened rfl carries (.unavailable equal.symm)
            exact ⟨.error failure, (Readings.BoundedPreparedSource.LaterMiss.check_error failure).symm⟩
        | some reset =>
            let resetData := SquareRoot.Replay.PreparedSourceReplay.Readiness.capture segment current request
              reset.owner inputs
            if checkedReset : resetData.Ready then
              have resetReady := resetData.ready_iff.mp checkedReset
              if resetCarries : variation < reset.owner.track.initial.clearance.bound then
                let accepted : Readings.BoundedPreparedSource.LaterAccepted segment current owner request variation :=
                  Readings.BoundedPreparedSource.LaterAccepted.moved ready carries reset equal.symm resetReady
                    resetCarries
                refine ⟨.ok accepted, ?_⟩
                unfold Readings.BoundedPreparedSource.checkLater
                rw [dif_pos ready, dif_neg carries]
                split
                · rename_i absent
                  cases absent.symm.trans equal.symm
                · rename_i other observed
                  have same := Option.some.inj (observed.symm.trans equal.symm)
                  cases same
                  rw [dif_pos resetReady, dif_pos resetCarries]
              else
                let failure : Readings.BoundedPreparedSource.LaterMiss segment current owner request variation :=
                  .exhausted ready strengthened rfl carries (.notCarrying reset equal.symm resetReady resetCarries)
                exact ⟨.error failure, (Readings.BoundedPreparedSource.LaterMiss.check_error failure).symm⟩
            else
              have resetReady : ¬ Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current reset.owner
                request :=
                fun ready => checkedReset (resetData.ready_iff.mpr ready)
              let failure : Readings.BoundedPreparedSource.LaterMiss segment current owner request variation :=
                .exhausted ready strengthened rfl carries (.notReady reset equal.symm resetReady)
              exact ⟨.error failure, (Readings.BoundedPreparedSource.LaterMiss.check_error failure).symm⟩
  else
    have ready : ¬ Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current owner request :=
      fun ready => checkedReady (readiness.ready_iff.mpr ready)
    let failure : Readings.BoundedPreparedSource.LaterMiss segment current owner request variation := .notReady ready
    exact .done ⟨.error failure, (Readings.BoundedPreparedSource.LaterMiss.check_error failure).symm⟩

/-- Consume the restored later stage. The coefficient cases then use the
original finite helper, which contains no further reset or winding search. -/
def afterMove (inputs : SquareRoot.Replay.PreparedSourceReplay.Inputs segment request.rootDiameter)
    (ready : Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current owner request)
    (inheritedMiss : ¬ Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < owner.track.initial.clearance.bound)
    (strengthened : Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval (segment.pointAt
      current.parameter)))
    (strengthened_eq : strengthened = SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner)
    (directMiss : ¬ Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < strengthened.track.initial.clearance.bound)
    (moving : Readings.BoundedPreparedSource.MoveMiss segment current owner request
      (Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter))
    (moved : Riemann.Branches.PreparedSheetContinuation.Owner (polynomial.eval (segment.pointAt current.parameter)))
    (moved_eq : moved = Riemann.Branches.PreparedSheetContinuation.recentered owner) :
    SquareRoot.Replay.MovingRecenterReplay.Plan (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      (polynomial.eval (segment.pointAt current.parameter)))
      (SquareRoot.Replay.MovingRecenterReplay.Checked (Readings.BoundedPreparedSource.afterMoveMiss segment current
        owner request ready inheritedMiss
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner) rfl (by
            rw [← strengthened_eq];
            exact directMiss) moving moved moved_eq)) 5 :=
  (SquareRoot.Replay.BoundedMovingReplay.later segment current moved request inputs
    (Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter)).map
      fun restored => by
    let value : SquareRoot.Replay.BoundedPreparedSourceReplay.Outcome segment current owner request := match
      restored.val with
      | .error later => Readings.BoundedPreparedSource.afterLaterMiss segment current owner request ready inheritedMiss
          strengthened strengthened_eq directMiss moving moved moved_eq (moved_eq ▸ later)
      | .ok (Readings.BoundedPreparedSource.LaterAccepted.strengthened movedReady value valueEq carries) =>
          .ok
            { cached :=
                { preparedOwner := value
                  preparedOwner_eq := by
                    have movedReady' : Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current
                      (Riemann.Branches.PreparedSheetContinuation.recentered owner) request :=
                      moved_eq ▸ movedReady
                    have movedMiss := fun carrying =>
                      Readings.BoundedPreparedSource.MoveMiss.not_carrying moving inheritedMiss ⟨movedReady',
                        carrying⟩
                    have canonical :=
                      Riemann.Branches.PreparedSheetContinuation.prepared_eq_strengthened_recentered_of_ready
                      segment current owner request ready inheritedMiss
                        (by rw [← strengthened_eq]; exact directMiss) movedReady' movedMiss
                        (by rw [← moved_eq, ← valueEq]; exact carries)
                    exact (valueEq.trans (congrArg
                      SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner moved_eq)).trans
                      canonical.symm }
              small := carries }
      | .ok (Readings.BoundedPreparedSource.LaterAccepted.moved movedReady strengthenedMiss reset found resetReady
        carries) =>
          .ok
            { cached :=
                { preparedOwner := reset.owner
                  preparedOwner_eq := by
                    have firstReady : Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current
                      (Riemann.Branches.PreparedSheetContinuation.recentered owner) request :=
                      moved_eq ▸ movedReady
                    have firstMiss := fun carrying =>
                      Readings.BoundedPreparedSource.MoveMiss.not_carrying moving inheritedMiss ⟨firstReady,
                        carrying⟩
                    have secondEq : Riemann.Branches.PreparedSheetContinuation.recentered
                      (Riemann.Branches.PreparedSheetContinuation.recentered owner) = reset.owner := by
                      rw [← moved_eq]
                      exact Riemann.Branches.PreparedSheetContinuation.recentered_eq_of_movingRecenter_eq_some moved
                        reset found
                    have canonical := Riemann.Branches.PreparedSheetContinuation.prepared_eq_recentered_twice_of_ready
                      segment current owner request ready inheritedMiss
                        (by rw [← strengthened_eq]; exact directMiss) firstReady firstMiss
                        (by rw [← moved_eq]; exact strengthenedMiss)
                        (by rw [secondEq]; exact resetReady) (by rw [secondEq]; exact carries)
                    exact (canonical.trans secondEq).symm }
              small := carries }
    refine ⟨value, ?_⟩
    cases strengthened_eq
    unfold Readings.BoundedPreparedSource.afterMoveMiss
    rw [← restored.property]
    rfl

/-- Complete both original moving branches from saved winding replies. The
result certifies the bounded check itself, including every finite miss. -/
def finishMoves (pending : SquareRoot.Replay.BoundedPreparedSourceReplay.PendingMoves segment current owner request)
    (restored : SquareRoot.Replay.MovingRecenterReplay.Checked
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenter? owner)) :
    SquareRoot.Replay.MovingRecenterReplay.Plan (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial
      (polynomial.eval (segment.pointAt current.parameter)))
      (SquareRoot.Replay.BoundedPreparedSourceReplay.Checked segment current owner request) 5 := by
  have ready := pending.readiness.ready_iff.mp pending.ready
  have inheritedMiss : ¬ Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter <
      owner.track.initial.clearance.bound := by
    rw [← pending.movement_eq, ← pending.readiness.clearance_eq]
    exact pending.inheritedMiss
  have directMiss : ¬ Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter <
      pending.strengthened.track.initial.clearance.bound := by
    rw [← pending.movement_eq]
    exact pending.strengthenedMiss
  have canonicalMiss : ¬ Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter <
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner).track.initial.clearance.bound
        := by
    rw [← pending.strengthened_eq]
    exact directMiss
  rcases restored with ⟨restored, equal⟩
  cases restored with
  | none =>
      have movedEq : owner = Riemann.Branches.PreparedSheetContinuation.recentered owner := by
        unfold Riemann.Branches.PreparedSheetContinuation.recentered; rw [← equal]
      exact (SquareRoot.Replay.BoundedMovingReplay.afterMove segment current owner request pending.readiness.inputs
        ready inheritedMiss pending.strengthened
        pending.strengthened_eq directMiss (.unavailable equal.symm) owner movedEq).map fun result =>
        ⟨result.val, by
          unfold Readings.BoundedPreparedSource.check
          rw [dif_pos ready, dif_neg inheritedMiss]
          dsimp only
          rw [dif_neg canonicalMiss]
          split
          · exact result.property.symm
          · rename_i reset observed
            cases equal.trans observed⟩
  | some reset =>
      have movedEq : reset.owner = Riemann.Branches.PreparedSheetContinuation.recentered owner :=
        (Riemann.Branches.PreparedSheetContinuation.recentered_eq_of_movingRecenter_eq_some owner reset equal.symm).symm
      let resetData := SquareRoot.Replay.PreparedSourceReplay.Readiness.capture segment current request reset.owner
        pending.readiness.inputs
      if checkedReset : resetData.Ready then
        have resetReady := resetData.ready_iff.mp checkedReset
        if resetCarries : Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
          request.endpoint.parameter <
            reset.owner.track.initial.clearance.bound then
          let accepted := Readings.BoundedPreparedSource.acceptedMove segment current owner request ready inheritedMiss
            canonicalMiss
            reset equal.symm resetReady resetCarries
          exact .done ⟨.ok accepted, by
            unfold Readings.BoundedPreparedSource.check
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
          exact (SquareRoot.Replay.BoundedMovingReplay.afterMove segment current owner request pending.readiness.inputs
            ready inheritedMiss pending.strengthened
            pending.strengthened_eq directMiss (.notCarrying reset equal.symm resetReady resetCarries)
            reset.owner movedEq).map fun result =>
            ⟨result.val, by
              unfold Readings.BoundedPreparedSource.check
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
        have resetReady : ¬ Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current reset.owner
          request :=
          fun ready => checkedReset (resetData.ready_iff.mpr ready)
        exact (SquareRoot.Replay.BoundedMovingReplay.afterMove segment current owner request pending.readiness.inputs
          ready inheritedMiss pending.strengthened
          pending.strengthened_eq directMiss (.notReady reset equal.symm resetReady)
          reset.owner movedEq).map fun result =>
          ⟨result.val, by
            unfold Readings.BoundedPreparedSource.check
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
