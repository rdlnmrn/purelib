module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay
public import Purelib.Riemann.Branches.PreparedSheetContinuation

import Purelib.Elab.Deriving.Repr
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

@[expose] public section

/-!
# Checked endpoint retention after a replayed parameter move

The endpoint of a prepared subdivision is not reserved transport alone:
`advanceCached` also retains, strengthens or recentres the transported owner
at a preparation floor.  This checker completes the first two branches and
returns the exact unresolved reset obligation in the third.  It never runs
that reset.  The source-state association remains a separate checked input.

Only existing finite transport and preparation modules are imported.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.PreparedRetainedTransportReplay

open Purelib.Riemann
open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay
  (Coordinate Gaussian Box Owner State)

variable {source target : Gaussian} {ambient :
  Box}
variable {state : State source ambient} {reserve :
  Coordinate}

/-- The successful endpoint-retention stage before any moving reset. -/
inductive Branch where
  /-- Retain the carried owner whose existing clearance meets the requested floor. -/ | inherited
  /-- Retain the coefficient-strengthened owner after the original bound misses the floor. -/ | coefficientStrengthened
deriving DecidableEq
derive_exposed_repr PreparedRetainedTransportReplay.Branch

set_option genInjectivity false in
/-- Both checked bounds and the refreshed owner are retained.  This proves
which reset the canonical constructor would select, not that it would fail. -/
structure NeedsReset (transport : PreparedOwnerTransportReplay.Checked state target reserve)
    (floor : Coordinate) where
  /-- The carried owner's retained original clearance reading. -/ originalBound :
    Coordinate
  /-- The original reading equals the carried owner's actual clearance. -/ originalBound_eq : originalBound =
    transport.value.track.initial.clearance.bound
  /-- The original carried clearance does not meet the requested floor. -/ originalMiss : ¬ floor ≤ originalBound
  /-- The actual coefficient-strengthened owner computed from the carried owner. -/ refreshed :
    Owner target
  /-- The retained refreshed owner equals the original coefficient-strengthening construction. -/ refreshed_eq :
    refreshed = Clearance.QuadraticCoefficientClearance.strengthen transport.value
  /-- The refreshed owner's retained clearance reading. -/ refreshedBound :
    Coordinate
  /-- The retained refreshed reading equals that exact owner's clearance. -/ refreshedBound_eq : refreshedBound =
    refreshed.track.initial.clearance.bound
  /-- The refreshed clearance still does not meet the requested floor. -/ refreshedMiss : ¬ floor ≤ refreshedBound

constructive_injectivity NeedsReset

/-- When both retained bound comparisons fail, the original endpoint-retention procedure selects its recentered owner.
-/
theorem NeedsReset.canonical_reset
    {transport : PreparedOwnerTransportReplay.Checked state target reserve} {floor :
      Coordinate}
    (report : NeedsReset transport floor) :
    PreparedSheetContinuation.retainedAtReserve transport.value floor =
      PreparedSheetContinuation.recentered transport.value := by
  have originalMiss : ¬ floor ≤ transport.value.track.initial.clearance.bound := by
    rw [← report.originalBound_eq]
    exact report.originalMiss
  have refreshedMiss : ¬ floor ≤
      (Clearance.QuadraticCoefficientClearance.strengthen transport.value).track.initial.clearance.bound :=
        by
    rw [← report.refreshed_eq, ← report.refreshedBound_eq]
    exact report.refreshedMiss
  unfold PreparedSheetContinuation.retainedAtReserve
  rw [if_neg originalMiss, if_neg refreshedMiss]

set_option genInjectivity false in
/-- The retained endpoint owner meeting the requested floor with its exact original branch identity.

Record the selected branch, its actual clearance reading and equality with the canonical endpoint-retention result. -/
structure Checked (transport : PreparedOwnerTransportReplay.Checked state target reserve)
    (floor : Coordinate) where
  /-- The actual successful endpoint-retention stage. -/ branch :
    Branch
  /-- The retained target owner selected by that stage. -/ value : Owner
    target
  /-- The clearance reading retained from the selected owner. -/ bound :
    Coordinate
  /-- The retained reading equals the selected owner's actual clearance. -/ bound_eq : bound =
    value.track.initial.clearance.bound
  /-- The selected owner's retained bound meets the requested floor. -/ enough : floor ≤ bound
  /-- The selected owner matches its branch and, for strengthening, retains the preceding original-bound miss. -/
    branch_correct : match branch with
    | .inherited => value = transport.value
    | .coefficientStrengthened =>
        value = Clearance.QuadraticCoefficientClearance.strengthen transport.value ∧
          ¬ floor ≤ transport.value.track.initial.clearance.bound
  /-- The selected owner equals the original canonical endpoint-retention result. -/ value_eq : value =
    PreparedSheetContinuation.retainedAtReserve transport.value floor

constructive_injectivity Checked

/-- Complete the canonical endpoint move when no moving reset is required.
The carried owner and a possible coefficient refresh are each computed once. -/
def retain (transport : PreparedOwnerTransportReplay.Checked state target reserve)
    (floor : Coordinate) : Except
      (NeedsReset transport floor)
      (Checked transport floor) :=
  let bound := transport.value.track.initial.clearance.bound
  if enough : floor ≤ bound then
    .ok
      { branch := .inherited
        value := transport.value
        bound := bound
        bound_eq := rfl
        enough := enough
        branch_correct := rfl
        value_eq := (PreparedSheetContinuation.retainedAtReserve_eq_self _ _ enough).symm }
  else
    let refreshed := Clearance.QuadraticCoefficientClearance.strengthen transport.value
    let refreshedBound := refreshed.track.initial.clearance.bound
    if refreshedEnough : floor ≤ refreshedBound then
      .ok
        { branch := .coefficientStrengthened
          value := refreshed
          bound := refreshedBound
          bound_eq := rfl
          enough := refreshedEnough
          branch_correct := ⟨rfl, enough⟩
          value_eq := (PreparedSheetContinuation.retainedAtReserve_eq_coefficientStrengthening
            _ _ enough refreshedEnough).symm }
    else
      .error
        { originalBound := bound
          originalBound_eq := rfl
          originalMiss := enough
          refreshed := refreshed
          refreshed_eq := rfl
          refreshedBound := refreshedBound
          refreshedBound_eq := rfl
          refreshedMiss := refreshedEnough }

/-- Inconclusivity identifies this actual finite check, including its cached
refresh.  The unexecuted moving reset is not labelled a failed root process. -/
theorem NeedsReset.retain_error
    {transport : PreparedOwnerTransportReplay.Checked state target reserve} {floor :
      Coordinate}
    (report : NeedsReset transport floor) :
      retain transport floor = .error report := by
  cases report with
  | mk originalBound originalBoundEq originalMiss refreshed refreshedEq
      refreshedBound refreshedBoundEq refreshedMiss =>
      cases originalBoundEq
      cases refreshedEq
      cases refreshedBoundEq
      unfold retain
      rw [dif_neg originalMiss, dif_neg refreshedMiss]

/-- The initial state's already checked association suffices for the whole
retained transport, regardless of the original incoming refinement function. -/
theorem Checked.eq_original (original : Owner source)
    (restored : PreparedRootStateReplay.Checked source original.ambient
      (PreparedRootStateReplay.capture original.track.initial))
    {transport : PreparedOwnerTransportReplay.Checked restored.state target reserve}
    {floor : Coordinate} (result :
      Checked transport floor) :
    result.value = PreparedSheetContinuation.retainedAtReserve
      (Clearance.ExactQuadraticOwnerClearance.reservedTransport original transport.targetNonzero
        (transport.originalSmall original restored) reserve) floor :=
  result.value_eq.trans (congrArg (fun owner => PreparedSheetContinuation.retainedAtReserve owner
    floor)
    (transport.eq_original original restored))

/-- This is the actual dependent successor index used by prepared spines,
including endpoint retention.  It does not merely identify a point query. -/
theorem Checked.eq_advanceCached
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {baseAmbient : Box} {start finish :
      Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial baseAmbient start finish)
    (within : segment.WithinAmbient) (left : ClearSheetContinuation.Subdivision.Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
    (request : PreparedSheetContinuation.StepRequest)
    (cached : PreparedSheetContinuation.CachedSource segment left owner request)
    (small : ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound)
    (restored : PreparedRootStateReplay.Checked (polynomial.eval (segment.pointAt left.parameter))
      cached.preparedOwner.ambient
      (PreparedRootStateReplay.capture cached.preparedOwner.track.initial))
    {transport : PreparedOwnerTransportReplay.Checked restored.state
      (polynomial.eval (segment.pointAt request.endpoint.parameter))
      (PreparedSheetContinuation.transportReserve segment left request)}
    (result : Checked transport
      (PreparedSheetContinuation.preparedClearanceLower segment left request)) :
    result.value = PreparedSheetContinuation.advanceCached segment within left owner request cached
      small :=
  result.eq_original cached.preparedOwner restored

section Spines

variable {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {baseAmbient : Box} {start finish :
    Gaussian}
  (segment : Geometry.ClearPath.ClearSegment polynomial baseAmbient start finish)
  (within : segment.WithinAmbient) (left : ClearSheetContinuation.Subdivision.Endpoint)
  (owner : Owner (polynomial.eval (segment.pointAt left.parameter)))
  (request : PreparedSheetContinuation.StepRequest)
  (cached : PreparedSheetContinuation.CachedSource segment left owner request)
  (ordered : left.parameter ≤ request.endpoint.parameter)
  (small : ClearSheetContinuation.variationBound segment left.parameter request.endpoint.parameter <
    cached.preparedOwner.track.initial.clearance.bound)
  (restored : PreparedRootStateReplay.Checked (polynomial.eval (segment.pointAt left.parameter))
    cached.preparedOwner.ambient (PreparedRootStateReplay.capture cached.preparedOwner.track.initial))
  {transport : PreparedOwnerTransportReplay.Checked restored.state
    (polynomial.eval (segment.pointAt request.endpoint.parameter))
    (PreparedSheetContinuation.transportReserve segment left request)}
  (result : Checked transport
    (PreparedSheetContinuation.preparedClearanceLower segment left request))

/-- Attach a restored tail at the exact canonical successor without executing
that successor again.  The only connection is an erased equality cast. -/
def Checked.prepend
    (remaining : PreparedSheetContinuation.Subdivision segment within request.endpoint result.value) :
    PreparedSheetContinuation.Subdivision segment within left owner :=
  PreparedSheetContinuation.Subdivision.nextCached segment within left owner request cached ordered
    small
    (by rw [← cached.preparedOwner_eq]; exact small)
    (remaining.castOwner (result.eq_advanceCached segment within left owner request cached small restored))

/-- Replay preserves the actual request list consumed by the bank-provenance
and uniqueness theorem, not just the number of accepted cells. -/
theorem Checked.prepend_requests
    (remaining : PreparedSheetContinuation.Subdivision segment within request.endpoint result.value) :
    (result.prepend segment within left owner request cached ordered small restored remaining).requests =
      request :: remaining.requests := by
  simp only [Checked.prepend,
    PreparedSheetContinuation.Subdivision.nextCached,
    PreparedSheetContinuation.Subdivision.requests_next,
    PreparedSheetContinuation.Subdivision.castOwner_requests, -eq_self, -iff_self]
  rfl

end Spines

end Purelib.RootIsolation.SquareRoot.Replay.PreparedRetainedTransportReplay
