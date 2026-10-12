module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.RootIsolation.SquareRoot.Owner.Transport

public import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

public section

/-!
# Terminal data retained during prepared acquisition

The canonical subdivision is proof-indexed by successive owner computations.
Reading its terminal owner can therefore replay those computations in compiled
code. This acquisition pass retains the endpoint and owner when they are first
computed, together with equality to the existing checker and terminal semantics.
Only the internal shorter-mesh attempt may fail; the public constructor has a
proved safe fallback and returns a certified successful acquisition.
-/

namespace Purelib.RootIsolation.SquareRoot.Preparation.Terminal

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib
open Purelib.RootIsolation

open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision StepRequest CachedSource advanceCached prepared)
open Purelib.Riemann.Paths.PreparedClearPathModels
  (Owner Endpoint zeroEndpoint oneEndpoint ownerAtStart CompleteSegment)

namespace TerminalAcquisition

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {start finish :
  Gaussian.Basic.Canonical}
  {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}

/-- Changing the initial owner along equality preserves the subdivision's terminal owner up to heterogeneous equality.

Eliminating the supplied owner equality leaves the same retained subdivision and terminal owner. Heterogeneous equality
records that the dependent terminal type is unchanged. -/
theorem castOwner_terminal_heq {left : Riemann.Paths.PreparedClearPathModels.Endpoint}
    {first second : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval (segment.pointAt left.parameter))}
    (equal : first = second) (subdivision : Riemann.Branches.PreparedSheetContinuation.Subdivision segment within left
      first) :
    HEq (subdivision.castOwner equal).terminalOwner subdivision.terminalOwner := by
  cases equal
  rfl

set_option genInjectivity false in
/-- A successful finite subdivision with its endpoint and terminal owner cached during execution.

The checker equation and exact owner identities specify these retained values without recomputing the dependent terminal
spine. -/
structure Execution (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Riemann.Paths.PreparedClearPathModels.Endpoint)
    (owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval (segment.pointAt left.parameter))) (requests :
      List Riemann.Branches.PreparedSheetContinuation.StepRequest) where
  /-- The retained subdivision produced by the original request list. -/ subdivision :
    Riemann.Branches.PreparedSheetContinuation.Subdivision segment within left owner
  /-- The original finite checker returns exactly the retained subdivision. -/ success :
    Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps segment within left owner requests = some
    subdivision
  /-- The terminal endpoint cached during execution. -/ endpoint : Riemann.Paths.PreparedClearPathModels.Endpoint
  /-- The retained subdivision ends at the cached endpoint. -/ endpoint_eq : subdivision.endpoint = endpoint
  /-- The actual terminal owner cached at that same endpoint. -/ terminalOwner :
    Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval (segment.pointAt endpoint.parameter))
  /-- The cached owner is heterogeneously equal to the original subdivision's terminal owner. -/ terminalOwner_heq : HEq
    terminalOwner subdivision.terminalOwner

constructive_injectivity Execution

set_option genInjectivity false in
/-- The exact result of a finite subdivision attempt, retaining success or the checker's failure equation.

An accepted result retains the actual successful execution. A declined result supplies the equation that the same finite
request checker returned no subdivision. -/
inductive Attempt (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Riemann.Paths.PreparedClearPathModels.Endpoint)
    (owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval (segment.pointAt left.parameter))) (requests :
      List Riemann.Branches.PreparedSheetContinuation.StepRequest) where
  /-- A successful execution retaining the actual subdivision, terminal endpoint and terminal owner. -/ | accepted
    (execution : SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution segment within left owner requests)
  /-- The exact original request checker returned no subdivision. -/ | declined (failure :
    Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps segment within left owner requests = none)

constructive_injectivity Attempt

/-- Execute the original request list while caching each source and the actual terminal owner.

An accepted tail is reused with its endpoint and owner identities; failed ordering or clearance checks retain the
corresponding checker failure. -/
@[expose] def attempt (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (left : Riemann.Paths.PreparedClearPathModels.Endpoint)
    (owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval (segment.pointAt left.parameter))) :
    (requests : List Riemann.Branches.PreparedSheetContinuation.StepRequest) →
      SquareRoot.Preparation.Terminal.TerminalAcquisition.Attempt segment within left owner requests
  | [] => .accepted ⟨.stop left owner, rfl, left, rfl, owner, HEq.rfl⟩
  | request :: remaining =>
      let cached := Riemann.Branches.PreparedSheetContinuation.CachedSource.canonical segment left owner request
      if ordered : left.parameter ≤ request.endpoint.parameter then
        if cachedSmall : Riemann.Branches.ClearSheetContinuation.variationBound segment
            left.parameter request.endpoint.parameter < cached.preparedOwner.track.initial.clearance.bound then
          have small : Riemann.Branches.ClearSheetContinuation.variationBound segment
              left.parameter request.endpoint.parameter < (prepared segment left owner
                request).track.initial.clearance.bound := by
            rw [cached.preparedOwner_eq] at cachedSmall
            exact cachedSmall
          let nextOwner := Riemann.Branches.PreparedSheetContinuation.advanceCached segment within left owner request
            cached cachedSmall
          match Purelib.RootIsolation.SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt segment within
            request.endpoint nextOwner remaining with
          | .declined failure => .declined (by
              rw [Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps, dif_pos ordered, dif_pos cachedSmall]
              dsimp only
              rw [failure])
          | .accepted tail => .accepted
              { subdivision := Riemann.Branches.PreparedSheetContinuation.Subdivision.nextCached segment within left
                  owner request cached ordered cachedSmall small tail.subdivision
                success := by
                  rw [Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps, dif_pos ordered, dif_pos
                    cachedSmall]
                  dsimp only
                  rw [tail.success]
                endpoint := tail.endpoint
                endpoint_eq := (Riemann.Branches.PreparedSheetContinuation.Subdivision.nextCached_endpoint ..).trans
                  tail.endpoint_eq
                terminalOwner := tail.terminalOwner
                terminalOwner_heq := tail.terminalOwner_heq.trans
                  (SquareRoot.Preparation.Terminal.TerminalAcquisition.castOwner_terminal_heq
                    (Riemann.Branches.PreparedSheetContinuation.advanceCached_eq_advance
                      segment within left owner request cached
                      cachedSmall small) tail.subdivision).symm }
        else .declined (by
            rw [Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps, dif_pos ordered, dif_neg cachedSmall])
      else .declined (by rw [Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps, dif_neg ordered])

end TerminalAcquisition

set_option genInjectivity false in
/-- A successful dyadic segment with its computed terminal owner cached.
The checker and owner equalities are specifications only, not runtime readers.

The depth, complete subdivision, request list and finishing owner are cached together. Their equations identify the
exact dyadic checker result and the same prepared segment owners. -/
structure AcquiredDyadic {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {start
  finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval start)) (diameter : Fraction.Rational)
      (positive : 0 < diameter) where
  /-- The dyadic depth used by the successful acquisition. -/ depth : Nat
  /-- The retained complete segment for the original path and initial owner. -/ prepared :
    Riemann.Paths.PreparedClearPathModels.CompleteSegment segment within owner
  /-- The original dyadic checker returns the retained prepared subdivision at this depth. -/ success :
    Riemann.Branches.PreparedSheetContinuation.Subdivision.tryDyadic segment within
    Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
    (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner)
    depth diameter positive = some prepared.subdivision
  /-- The exact request list retained by this successful acquisition. -/ requests : List
    Riemann.Branches.PreparedSheetContinuation.StepRequest
  /-- The cached requests equal the retained subdivision's original requests. -/ requests_eq : requests =
    prepared.subdivision.requests
  /-- The actual finishing root owner cached during acquisition. -/ finishOwner :
    Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval finish)
  /-- The cached finishing owner equals the prepared segment's original finishing owner. -/ finishOwner_eq : finishOwner
    = prepared.finishOwner

constructive_injectivity AcquiredDyadic

namespace AcquiredDyadic

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {start finish :
  Gaussian.Basic.Canonical}
  {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
  {owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval start)} {diameter : Fraction.Rational} {positive
    : 0 < diameter}

/-- Package a successful execution on the exact dyadic request list as a complete acquired segment.

The cached terminal owner is transported only along the proved endpoint equality and retained with its exact
prepared-owner identity. -/
@[expose] def ofExecution (depth : Nat) (requests : List Riemann.Branches.PreparedSheetContinuation.StepRequest)
    (requests_eq : requests = Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicRequests depth
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint diameter
      positive)
    (execution : SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution segment within
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment
      owner)
      requests) :
    SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner diameter positive := by
  have success : Riemann.Branches.PreparedSheetContinuation.Subdivision.tryDyadic segment within
    Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
    (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner)
      depth diameter positive = some execution.subdivision := by
    rw [Riemann.Branches.PreparedSheetContinuation.Subdivision.tryDyadic, ← requests_eq]
    exact execution.success
  let prepared := Riemann.Paths.PreparedClearPathModels.CompleteSegment.ofTryDyadic segment within owner depth diameter
    positive success
  have endpointEq : segment.pointAt execution.endpoint.parameter = finish := by
    rw [← execution.endpoint_eq]
    exact prepared.finish_eq
  let terminal : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval finish) :=
    SquareRoot.Owner.Transport.castOwnerParameter (congrArg polynomial.eval endpointEq) execution.terminalOwner
  exact
    { depth := depth
      prepared := prepared
      success := success
      requests := requests
      requests_eq := (Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps_requests segment within
        Riemann.Paths.PreparedClearPathModels.zeroEndpoint (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment
        owner)
        requests execution.success).symm
      finishOwner := terminal
      finishOwner_eq := eq_of_heq
        ((SquareRoot.Owner.Transport.castOwnerParameter_heq _ _).trans
          (execution.terminalOwner_heq.trans prepared.finishOwner_heq_terminalOwner.symm)) }

/-- Acquire a successful dyadic segment at the preferred or certified safe depth.

The preferred request list is attempted only when its depth is smaller. Success reuses its cached execution; otherwise
the certified safe request list supplies the fallback without rereading the dependent terminal spine. -/
@[expose] def acquire (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within :
  segment.WithinAmbient)
    (owner : Riemann.Paths.PreparedClearPathModels.Owner (polynomial.eval start)) (diameter : Fraction.Rational)
      (positive : 0 < diameter)
    (preferredDepth safeDepth : Nat)
    (safe : Riemann.Branches.PreparedSheetContinuation.Subdivision.DyadicMeshSafe segment
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
      (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner)
      safeDepth diameter positive) :
    { result : SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner diameter positive //
      result.depth = preferredDepth ∨ result.depth = safeDepth } :=
  let fallback : Unit → { result : SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner diameter positive
    //
      result.depth = preferredDepth ∨ result.depth = safeDepth } := fun _ =>
    let requests := Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicRequests safeDepth
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint diameter
      positive
    match SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt segment within
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment
      owner)
        requests with
    | .accepted execution => ⟨ofExecution safeDepth requests rfl execution, Or.inr rfl⟩
    | .declined failure => False.elim (by
        have success := Riemann.Branches.PreparedSheetContinuation.Subdivision.tryDyadic_eq_some_checkedDyadic segment
          within Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
          (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner) safeDepth diameter positive safe
        rw [Riemann.Branches.PreparedSheetContinuation.Subdivision.tryDyadic, failure] at success
        cases success)
  if preferredDepth < safeDepth then
    let requests := Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicRequests preferredDepth
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint diameter
      positive
    match SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt segment within
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment
      owner)
        requests with
    | .accepted execution => ⟨ofExecution preferredDepth requests rfl execution, Or.inl rfl⟩
    | .declined _ => fallback ()
  else fallback ()

end AcquiredDyadic

end Purelib.RootIsolation.SquareRoot.Preparation.Terminal
