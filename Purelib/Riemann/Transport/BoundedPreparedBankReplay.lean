module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Owner.Transport

import Purelib.RootIsolation.SquareRoot.Replay.BoundedPreparedSourceReplay
public import Purelib.Riemann.Readings.BoundedPreparedBanks
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRetainedTransportReplay

public section

/-!
Assemble the bounded bank scanner from checked source outcomes and retained
successors.  Both accepted spines and rejected prefixes identify the original
scanner, so a replayed miss may justify advancing the adaptive depth.  The
successor owner is supplied with an exact equation and is not regenerated.
-/

namespace Purelib.Riemann.Transport.BoundedPreparedBankReplay

open Purelib.Riemann.Branches.PreparedSheetContinuation
  (Coordinate Owner Endpoint StepRequest Subdivision advanceCached
    retainedAtReserve preparedClearanceLower)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedClearPathModels
  (GaussianPolynomial Gaussian Box CompleteSegment PreparedPath zeroEndpoint oneEndpoint ownerAtStart)
open Purelib.Riemann.Readings.BoundedPreparedBanks (StepFailure StepSuccess PathFailure PathSuccess)
open Purelib.Riemann.Readings
open Purelib.Riemann.Integration

variable {polynomial : GaussianPolynomial} {ambient : Box}

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Stationary cached transport retains the original prepared owner and its refiner.

Equality of the endpoint polynomial values identifies the successor with the original owner cast to the target and
retained at the requested reserve. -/
theorem advanceCached_stationary {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (accepted : BoundedPreparedSource.Accepted segment current owner request)
    (same : polynomial.eval (segment.pointAt current.parameter) = polynomial.eval (segment.pointAt
      request.endpoint.parameter)) :
    advanceCached segment within current owner request accepted.cached accepted.small =
      retainedAtReserve (same ▸ accepted.cached.preparedOwner) (preparedClearanceLower segment current request) := by
  unfold advanceCached ExactQuadraticOwnerClearance.reservedTransport
  rw [dif_pos same]

/-- Force only the selected failure thunk, leaving successful values unchanged. -/
@[expose] def forceFailure {α β : Type} : Except (Thunk α) β → Except α β
  | .error failure => .error failure.get
  | .ok accepted => .ok accepted

section
open Purelib.Polynomial
/-- The exact indexed step success or deferred failure of a bounded request scan. -/
abbrev StepOutcome {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest) :=
  Except (Thunk (StepFailure segment within current owner requests)) (StepSuccess segment within current owner requests)

/-- A retained step outcome with equality to the original bounded request scanner. -/
abbrev StepChecked {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (requests : List StepRequest) :=
  {value : StepOutcome segment within current owner requests //
    BoundedPreparedBanks.steps segment within current owner requests = forceFailure value}

/-- The exact prepared owner type at the current segment parameter. -/
@[reducible, expose] def CurrentOwner {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint) :=
  Owner (polynomial.eval (segment.pointAt current.parameter))

/-- The exact prepared owner type at the requested segment endpoint. -/
@[reducible, expose] def TargetOwner {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (request : StepRequest) :=
  Owner (polynomial.eval (segment.pointAt request.endpoint.parameter))

/-- The original accepted bounded source certificate for this owner and request. -/
@[reducible, expose] def AcceptedSource {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : CurrentOwner segment current) (request : StepRequest) :=
  BoundedPreparedSource.Accepted segment current owner request

/-- Equality of a retained successor with advancement using the actual accepted cached source. -/
@[reducible, expose] def SuccessorIdentity {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (current : Endpoint) (owner : CurrentOwner segment current) (request : StepRequest)
    (accepted : AcceptedSource segment current owner request) (next : TargetOwner segment request) : Prop :=
  next = advanceCached segment within current owner request accepted.cached accepted.small

end

open Purelib.Polynomial in
set_option genInjectivity false in
/-- A successor owner tied to the original initial owner and accepted source.

The record retains each actual value with its exact identity and certifies that the successor is the result of advancing
the accepted cache. -/
structure Successor {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (current : Endpoint) (owner : CurrentOwner segment current) (request : StepRequest)
    (accepted : AcceptedSource segment current owner request) where
  /-- The retained initial prepared owner. -/ initial : CurrentOwner segment current
  /-- The retained initial owner is the supplied original owner. -/ initial_eq : initial = owner
  /-- The actual accepted source for the retained initial owner. -/ source : AcceptedSource segment current owner
    request
  /-- The retained source is the supplied original accepted certificate. -/ source_eq : source = accepted
  /-- The retained successor owner at the request endpoint. -/ value : TargetOwner segment request
  /-- The successor equals advancement through the original accepted cache. -/ value_eq : SuccessorIdentity segment
    within current owner request accepted value

constructive_injectivity Successor

section
open Purelib.Polynomial
/-- Package an existing successor and its exact cached-advancement equation.

The construction retains the supplied owner and accepted source without executing advancement again. -/
@[expose] def Successor.ofExisting {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (current : Endpoint) (owner : CurrentOwner segment current) (request : StepRequest)
    (accepted : AcceptedSource segment current owner request) (next : TargetOwner segment request)
    (nextEq : SuccessorIdentity segment within current owner request accepted next) :
    Successor segment within current owner request accepted :=
  ⟨owner, rfl, accepted, rfl, next, nextEq⟩

/-- Transport a checked tail across equality of its original prepared owners. -/
@[expose] def StepChecked.reindexOwner {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {current : Endpoint} {first last : CurrentOwner segment current}
    {requests : List StepRequest} (equal : first = last)
    (tail : StepChecked segment within current first requests) :
    StepChecked segment within current last requests :=
  equal ▸ tail

/-- Attach a checked tail to the canonical advancement represented by the retained successor. -/
@[expose] def Successor.attach {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {current : Endpoint} {owner : CurrentOwner segment current} {request : StepRequest}
    {accepted : AcceptedSource segment current owner request} {requests : List StepRequest}
    (successor : Successor segment within current owner request accepted)
    (tail : StepChecked segment within request.endpoint successor.value requests) :
    StepChecked segment within request.endpoint
      (advanceCached segment within current owner request accepted.cached accepted.small) requests :=
  StepChecked.reindexOwner successor.value_eq tail

end

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Owner in
/-- Retain the original owner for a stationary polynomial-value step.

The endpoint cast preserves the complete prepared owner and history, and the retained reserve determines the exact
successor identity. -/
theorem Successor.stationary {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
    {current : Endpoint} {owner : CurrentOwner segment current} {request : StepRequest}
    {accepted : AcceptedSource segment current owner request}
    (successor : Successor segment within current owner request accepted)
    (same : polynomial.eval (segment.pointAt current.parameter) =
      polynomial.eval (segment.pointAt request.endpoint.parameter)) :
    successor.value = retainedAtReserve
      (Transport.castOwnerParameter same accepted.cached.preparedOwner)
      (preparedClearanceLower segment current request) :=
  successor.value_eq.trans (advanceCached_stationary segment within current owner request accepted same)

section
open Purelib.Polynomial
/-- Certify the successful empty scan with the original stopping subdivision. -/
@[expose] def stop {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    StepChecked segment within current owner [] := ⟨.ok ⟨.stop current owner, rfl⟩, rfl⟩

/-- Retain a lazy step rejection with its exact original scanner equation. -/
@[expose] def rejected {start finish : Gaussian} {segment : Geometry.ClearPath.ClearSegment polynomial ambient start
  finish}
    {within : segment.WithinAmbient} {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))} {requests : Thunk (List StepRequest)}
    (failure : Thunk (StepFailure segment within current owner requests.get)) :
    StepChecked segment within current owner requests.get := ⟨.error failure, failure.get.steps_error⟩

end

open Purelib.Polynomial in
open Purelib.Riemann in
/-- Prepend the actual accepted cached step to a checked request tail.

The exact successor equation transports the tail to the original scanner owner. Success retains the cached subdivision;
failure retains the visited step and defers only the unresolved tail. -/
@[expose] def prepend {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (requests : Thunk (List StepRequest))
    (ordered : current.parameter ≤ request.endpoint.parameter)
    (accepted : BoundedPreparedSource.Accepted segment current owner request)
    (found : BoundedPreparedSource.check segment current owner request = .ok accepted)
    (next : Owner (polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (nextEq : next = advanceCached segment within current owner request accepted.cached accepted.small)
    (tail : StepChecked segment within request.endpoint next requests.get) :
    StepChecked segment within current owner (request :: requests.get) := by
  let successor := Successor.ofExisting segment within current owner request accepted next nextEq
  let aligned := successor.attach tail
  rcases aligned with ⟨value, equal⟩
  cases value with
  | error failure =>
      exact rejected (requests := .mk fun _ => request :: requests.get)
        (.mk fun _ => .next current owner request requests.get ordered accepted found failure.get)
  | ok rest =>
      let combined : StepSuccess segment within current owner (request :: requests.get) :=
        ⟨Subdivision.nextCached segment within current owner request accepted.cached ordered
            accepted.small accepted.canonical_small rest.subdivision,
          Readings.BoundedPreparedBanks.prepend_success segment within current owner request requests.get ordered
            accepted rest⟩
      refine ⟨.ok combined, ?_⟩
      unfold BoundedPreparedBanks.steps
      rw [dif_pos ordered]
      split
      · rename_i failure observed
        cases observed.symm.trans found
      · rename_i other observed
        have same := Except.ok.inj (observed.symm.trans found)
        cases same
        rw [equal]
        rfl

/-- The original ordered dyadic requests for the specified segment, depth and diameter. -/
abbrev Requests (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter) :=
  Subdivision.dyadicRequests depth zeroEndpoint oneEndpoint diameter positive

open Purelib.Polynomial in
open Purelib.Riemann in
/-- Complete the retained first step using the original bounded path scanner. -/
@[expose] def head {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    (accepted : StepSuccess segment within zeroEndpoint (ownerAtStart segment owner) (Requests depth diameter positive))
      :
    CompleteSegment segment within owner :=
  Readings.BoundedPreparedBanks.completeHead segment within owner depth diameter positive accepted

section
open Purelib.Polynomial
/-- The actual bounded path success or deferred indexed path failure. -/
abbrev PathOutcome (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    {start finish : Gaussian} (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start)) :=
  Except (Thunk (PathFailure depth diameter positive path within owner)) (PathSuccess depth diameter positive path
    within owner)

/-- A retained path outcome with equality to the original bounded path scanner. -/
abbrev PathChecked (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    {start finish : Gaussian} (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start)) :=
  {value : PathOutcome depth diameter positive path within owner //
    BoundedPreparedBanks.path depth diameter positive path within owner = forceFailure value}

/-- Certify a deferred path rejection by the original scanner equation. -/
@[expose] def pathRejected {depth : Nat} {diameter : Coordinate} {positive : 0 < diameter}
    {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
    {within : path.WithinAmbient} {owner : Owner (polynomial.eval start)}
    (failure : Thunk (PathFailure depth diameter positive path within owner)) :
    PathChecked depth diameter positive path within owner := ⟨.error failure, failure.get.path_error⟩

end

open Purelib.Polynomial in
open Purelib.Polynomial.Geometry in
open Purelib.Riemann in
/-- Prepend an accepted segment to a checked path tail at its actual finishing owner.

The construction retains the original completed head. Tail failure records that visited head, while success constructs
the original prepared path with the same caches. -/
@[expose] def pathPrepend (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    {start middle finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (path : Polynomial.Geometry.ClearPath polynomial ambient middle finish) (within :
      (Polynomial.Geometry.ClearPath.cons segment
      path).WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (accepted : StepSuccess segment within.head zeroEndpoint (ownerAtStart segment owner) (Requests depth diameter
      positive))
    (found : BoundedPreparedBanks.steps segment within.head zeroEndpoint (ownerAtStart segment owner)
      (Requests depth diameter positive) = .ok accepted)
    (tail : PathChecked depth diameter positive path within.tail
      (head segment within.head owner depth diameter positive accepted).finishOwner) :
    PathChecked depth diameter positive (.cons segment path) within owner := by
  rcases tail with ⟨value, equal⟩
  cases value with
  | error failure => exact pathRejected (.mk fun _ => .tail segment path within owner accepted found failure.get)
  | ok rest =>
      let combined : PathSuccess depth diameter positive (.cons segment path) within owner :=
        ⟨.cons segment path owner within.head (head segment within.head owner depth diameter positive accepted)
          rest.prepared,
          Readings.BoundedPreparedBanks.prepend_path_success segment path within owner depth diameter positive accepted
            rest⟩
      refine ⟨.ok combined, ?_⟩
      unfold BoundedPreparedBanks.path
      dsimp only [head] at equal
      split
      · rename_i failure observed
        cases observed.symm.trans found
      · rename_i other observed
        have same := Except.ok.inj (observed.symm.trans found)
        cases same
        rw [equal]
        rfl

end Purelib.Riemann.Transport.BoundedPreparedBankReplay
