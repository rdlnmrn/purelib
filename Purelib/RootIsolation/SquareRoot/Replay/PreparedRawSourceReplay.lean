module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
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

open Purelib.RootIsolation

public section

/-!
# Canonical preparation from a restored raw state

The first successful diameter attempt can identify the canonical prepared
owner without reconstructing the incoming refiner or original side bounds.
The raw checkpoint must still be associated with that incoming source.  This
module does not infer canonical source provenance from numerical metadata.
Ready inputs and missed bounded attempts do not start uniform preparation or
the remaining retries: they return the checked unresolved branch instead.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.PreparedRawSourceReplay

open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Replay
open Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
open Purelib.Riemann.Branches.PreparedSheetContinuation
  (StepRequest AlreadyPrepared prepared prepared_eq_checked_of_not_ready)

variable {polynomial : SquareRoot.Replay.PreparedSourceReplay.Polynomial} {ambient : Box} {start finish : Gaussian}
variable (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
variable (current : Endpoint)
variable (source : Owner (polynomial.eval (segment.pointAt current.parameter)))
variable (request : Riemann.Branches.PreparedSheetContinuation.StepRequest)
variable {rootAmbient : Box}
variable (restored : SquareRoot.Replay.PreparedRawStateReplay.Checked _ rootAmbient
  (SquareRoot.Replay.PreparedRawStateReplay.capture source.track.initial))
variable (sameAmbient : rootAmbient = source.ambient)

/-- Construct the deferred quadratic representative from the restored raw-state checkpoint.

It supplies executable input to replay without claiming the original incoming track's refinement history. -/
@[expose] def representative : Owner (polynomial.eval (segment.pointAt current.parameter)) :=
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState source.parameterNonzero restored.representative

/-- Readiness uses only the raw box and boundary, so its decision does not
need the unknown incoming refinement function or original side numbers. -/
theorem ready_iff (sameAmbient : rootAmbient = source.ambient) :
    Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current
      (SquareRoot.Replay.PreparedRawSourceReplay.representative segment current source restored) request ↔
      Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current source request := by
  cases sameAmbient
  have same := restored.raw_eq_original source.track.initial
  have box := congrArg (fun state => state.box) same
  have boundary := congrArg (fun state => state.clearance.bound) same
  change restored.representative.box = source.track.initial.box at box
  change restored.representative.clearance.bound = source.track.initial.clearance.bound at boundary
  change (restored.representative.box.diagonalSq < request.rootDiameter ∧
    Riemann.RootContinuation.UniformSquareRootPreparation.predictedClearance segment request.rootDiameter ≤
      restored.representative.clearance.bound ∧
    restored.representative.box.Refines (Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment)) ↔ _
  rw [boundary, box]
  rfl

/-- The optional diameter attempt has the same target-owner values for the restored representative and original source.
-/
theorem attempt_values_eq (sameAmbient : rootAmbient = source.ambient) :
    ((Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment current.parameter
      (SquareRoot.Replay.PreparedRawSourceReplay.representative segment current source restored)
        request.rootDiameter).value).map (fun result => result.value) =
    ((Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment current.parameter source
      request.rootDiameter).value).map
      (fun result => result.value) := by
  cases sameAmbient
  exact restored.attemptValues_eq_original segment current.parameter source request.rootDiameter

/-- Projected optional output suffices for the canonical branch equation.
No decision procedure on whole owners or their function fields is needed. -/
theorem prepared_eq_of_attempt_value
    (notReady : ¬ Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current source request)
    (candidate : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (found : ((Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment current.parameter source
      request.rootDiameter).value).map (fun result => result.value) = some candidate)
    (carries : Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter < candidate.track.initial.clearance.bound) :
    Riemann.Branches.PreparedSheetContinuation.prepared segment current source request = candidate := by
  cases attempt : (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment current.parameter source
      request.rootDiameter).value with
  | none => simp only [attempt, Option.map] at found; cases found
  | some accepted =>
      simp only [attempt, Option.map, -eq_self, -iff_self] at found
      have candidateEqual := Option.some.inj found
      cases candidateEqual
      exact Riemann.Branches.PreparedSheetContinuation.prepared_eq_checked_of_not_ready segment current source request
        notReady accepted attempt carries

set_option genInjectivity false in
/-- Retained reasons why the first raw-source replay route has not produced an accepted cache.

Keep the actual readiness readings, failed attempt equation or noncarrying candidate without asserting failure of the
original total preparation. -/
inductive Inconclusive where
  /-- The restored representative is already ready, so the original inherited owner requires information beyond this
    first-attempt replay route. -/ | alreadyReady
      (data : SquareRoot.Replay.PreparedSourceReplay.Readiness segment current request
        (SquareRoot.Replay.PreparedRawSourceReplay.representative segment current source restored))
      (ready : data.Ready)
  /-- Retain failed readiness and the exact diameter-attempt equation returning no candidate. -/ | attemptMiss
      (data : SquareRoot.Replay.PreparedSourceReplay.Readiness segment current request
        (SquareRoot.Replay.PreparedRawSourceReplay.representative segment current source restored))
      (notReady : ¬ data.Ready)
      (procedure : (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment current.parameter
        (SquareRoot.Replay.PreparedRawSourceReplay.representative segment current source restored)
        request.rootDiameter).value
          = none)
  /-- Retain the actual diameter candidate, successful attempt equation and failed movement-versus-clearance comparison.
  -/
  | doesNotCarry
      (candidate : Riemann.RootContinuation.CheckedSquareRootPreparation.Result segment current.parameter
        (SquareRoot.Replay.PreparedRawSourceReplay.representative segment current source restored) request.rootDiameter)
      (procedure : (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment current.parameter
        (SquareRoot.Replay.PreparedRawSourceReplay.representative segment current source restored)
        request.rootDiameter).value
          = some candidate)
      (movement : Coordinate)
      (movement_eq : movement = Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
        request.endpoint.parameter)
      (failed : ¬ movement < candidate.value.track.initial.clearance.bound)

constructive_injectivity Inconclusive

/-- Return the same canonical cache consumed by prepared edges.  The only
executable owner input is the restored representative.  The original source
is used to index proofs; no original refinement or canonical preparation runs.
Inconclusivity certifies this first-attempt route only, not the total process.
-/
@[expose] def replay :
    Except (SquareRoot.Replay.PreparedRawSourceReplay.Inconclusive segment current source request restored)
      (SquareRoot.Replay.PreparedSourceReplay.Accepted segment current source request) := by
  let owner := SquareRoot.Replay.PreparedRawSourceReplay.representative segment current source restored
  let data := SquareRoot.Replay.PreparedSourceReplay.Readiness.capture segment current request owner
    (SquareRoot.Replay.PreparedSourceReplay.Inputs.capture segment request.rootDiameter)
  if ready : data.Ready then
    exact .error (.alreadyReady data ready)
  else
    have notReady : ¬ Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current source request := fun
      originalReady =>
      ready (data.ready_iff.mpr ((SquareRoot.Replay.PreparedRawSourceReplay.ready_iff segment current source request
        restored sameAmbient).mpr originalReady))
    exact
      match attempt : (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment current.parameter owner
        request.rootDiameter).value with
      | none => .error (.attemptMiss data ready attempt)
      | some candidate =>
          let movement := Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
            request.endpoint.parameter
          if carries : movement < candidate.value.track.initial.clearance.bound then
            .ok
              { cached :=
                  { preparedOwner := candidate.value
                    preparedOwner_eq := by
                      apply (SquareRoot.Replay.PreparedRawSourceReplay.prepared_eq_of_attempt_value segment current
                        source request notReady
                        candidate.value ?_ carries).symm
                      rw [← SquareRoot.Replay.PreparedRawSourceReplay.attempt_values_eq segment current source request
                        restored sameAmbient]
                      change ((Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment current.parameter
                        owner
                        request.rootDiameter).value).map (fun result => result.value) = some candidate.value
                      rw [attempt]
                      rfl }
                movement := movement
                movement_eq := rfl
                clearance := candidate.value.track.initial.clearance.bound
                clearance_eq := rfl
                carries := carries }
          else .error (.doesNotCarry candidate attempt movement rfl carries)

end Purelib.RootIsolation.SquareRoot.Replay.PreparedRawSourceReplay

end
