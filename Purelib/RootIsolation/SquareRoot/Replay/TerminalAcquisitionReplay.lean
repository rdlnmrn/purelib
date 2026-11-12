module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.PreparedClearPathModels
public import Purelib.RootIsolation.SquareRoot.Preparation.Terminal
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

open Purelib.RootIsolation.SquareRoot.Preparation.Terminal

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

public section

/-! Reassemble the canonical terminal acquisition from checked source caches
and successor owners. Its accepted outcome retains the computed terminal owner;
its declined outcome proves failure of this exact finite request list. -/
namespace Purelib.RootIsolation.SquareRoot.Replay.TerminalAcquisitionReplay

open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation
  (StepRequest CachedSource advanceCached advanceCached_eq_advance
    retainedAtReserve prepared Subdivision)
open Purelib.Riemann.Paths.PreparedClearPathModels
  (GaussianPolynomial Gaussian Box Owner Endpoint zeroEndpoint oneEndpoint ownerAtStart CompleteSegment)

attribute [local irreducible] advanceCached
  retainedAtReserve

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)

/-- The original checked acquisition attempt for the exact initial owner and finite request list. -/
abbrev Outcome (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) (requests : List
      StepRequest) :=
  TerminalAcquisition.Attempt segment within current owner requests

/-- A retained acquisition outcome with equality to the original finite execution. -/
abbrev Checked (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) (requests : List
      StepRequest) :=
  {value : Outcome segment within current owner requests //
    value = TerminalAcquisition.attempt segment within current owner requests}

/-- Restore the empty-request execution with its original endpoint and owner. -/
@[expose] def stop (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    Checked segment within current owner [] :=
  ⟨TerminalAcquisition.Attempt.accepted
    (Preparation.Terminal.TerminalAcquisition.Execution.mk (.stop current owner) rfl current rfl owner
    HEq.rfl), rfl⟩

/-- Restore a declined attempt whose first requested endpoint precedes the current parameter. -/
@[expose] def unordered (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (requests : List
      StepRequest)
    (miss : ¬ current.parameter ≤ request.endpoint.parameter) :
    Checked segment within current owner (request :: requests) := by
  refine ⟨TerminalAcquisition.Attempt.declined ?_, ?_⟩
  · simp only [Subdivision.trySteps, dif_neg miss, -eq_self]
    rfl
  · dsimp only [TerminalAcquisition.attempt]
    simp only [dif_neg miss, -eq_self]
    rfl

/-- Restore a declined attempt whose first variation bound fails the cached source's clearance test. -/
@[expose] def tooLarge (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (requests : List
      StepRequest)
    (cached : CachedSource segment current owner request)
    (ordered : current.parameter ≤ request.endpoint.parameter)
    (miss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound) :
    Checked segment within current owner (request :: requests) := by
  have same := cached.eq_canonical
  cases same
  refine ⟨TerminalAcquisition.Attempt.declined ?_, ?_⟩
  · rw [Subdivision.trySteps, dif_pos ordered, dif_neg miss]
  · dsimp only [TerminalAcquisition.attempt]
    simp only [dif_pos ordered, dif_neg miss, -eq_self]
    rfl

/-- Prepend one checked cached-source step to an exactly restored tail execution.

The successor owner must equal the original cached advance; both accepted and declined tails preserve the original full
execution. -/
@[expose] def prepend (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (requests : List
      StepRequest)
    (cached : CachedSource segment current owner request)
    (ordered : current.parameter ≤ request.endpoint.parameter)
    (small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter
      <
      cached.preparedOwner.track.initial.clearance.bound)
    (next : Owner (polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (nextEq : next = advanceCached segment within current owner request
      cached small)
    (tail : Checked segment within request.endpoint next requests) :
    Checked segment within current owner (request :: requests) := by
  cases nextEq
  have canonicalSmall : ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter <
      (prepared segment current owner request).track.initial.clearance.bound
        := by
    rw [← cached.preparedOwner_eq]
    exact small
  have same := cached.eq_canonical
  cases same
  rcases tail with ⟨tail, tailEq⟩
  cases tail with
  | declined failure =>
      refine ⟨TerminalAcquisition.Attempt.declined ?_, ?_⟩
      · rw [Subdivision.trySteps, dif_pos ordered, dif_pos small]
        dsimp only
        rw [failure]
      · dsimp only [TerminalAcquisition.attempt]
        simp only [dif_pos ordered, dif_pos small, ← tailEq, -eq_self]
        rfl
  | accepted rest =>
      refine ⟨TerminalAcquisition.Attempt.accepted
        (Preparation.Terminal.TerminalAcquisition.Execution.mk
        (Subdivision.nextCached segment within current owner request
          (CachedSource.canonical segment current owner request) ordered
            small canonicalSmall (TerminalAcquisition.Execution.subdivision rest))
        ?_ (TerminalAcquisition.Execution.endpoint rest)
          ((Subdivision.nextCached_endpoint ..).trans
          (TerminalAcquisition.Execution.endpoint_eq rest))
        (TerminalAcquisition.Execution.terminalOwner rest) ?_), ?_⟩
      · rw [Subdivision.trySteps, dif_pos ordered, dif_pos small]
        dsimp only
        rw [(TerminalAcquisition.Execution.success rest)]
      · exact (TerminalAcquisition.Execution.terminalOwner_heq rest).trans
          (TerminalAcquisition.castOwner_terminal_heq
          (advanceCached_eq_advance segment within current owner request
            (CachedSource.canonical segment current owner request) small
              canonicalSmall)
          (TerminalAcquisition.Execution.subdivision rest)).symm
      · dsimp only [TerminalAcquisition.attempt]
        simp only [dif_pos ordered, dif_pos small, ← tailEq, -eq_self]
        rfl

/-- Successful acquisitions at one depth have the same entire retained data,
including their request list and terminal owner. -/
theorem acquired_eq_of_depth {owner : Owner (polynomial.eval start)} {diameter : Fraction.Rational}
    {positive : 0 < diameter}
    (first second : Preparation.Terminal.AcquiredDyadic segment within owner diameter positive)
    (same : first.depth = second.depth) : first = second := by
  cases first with
  | mk firstDepth firstPrepared firstSuccess firstRequests firstRequestsEq firstOwner firstOwnerEq =>
    cases second with
    | mk secondDepth secondPrepared secondSuccess secondRequests secondRequestsEq secondOwner secondOwnerEq =>
      dsimp only at same
      cases same
      have spine := Option.some.inj (firstSuccess.symm.trans secondSuccess)
      have preparedEq : firstPrepared = secondPrepared := by
        cases firstPrepared
        cases secondPrepared
        cases spine
        rfl
      cases preparedEq
      cases firstRequestsEq
      cases secondRequestsEq
      cases firstOwnerEq
      cases secondOwnerEq
      rfl

set_option genInjectivity false in
/-- A finite attempt reports its checked failure or a complete acquisition at
the requested depth; neither case substitutes a different mesh. -/
inductive DepthResult (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (depth : Nat) where
  /-- A complete retained acquisition whose actual depth equals the original requested depth. -/ | accepted (value :
    Preparation.Terminal.AcquiredDyadic segment within owner diameter positive) (same : value.depth = depth)
  /-- The original dyadic checker returned no subdivision at the exact requested depth. -/ | declined (failure :
    Subdivision.tryDyadic segment within
    zeroEndpoint oneEndpoint
      (ownerAtStart segment owner) depth diameter positive = none)

constructive_injectivity DepthResult

/-- A successful acquisition at the safe depth equals the original safe-depth constructor's complete retained result. -/
theorem acquired_eq_safe (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (depth : Nat)
    (safe : Subdivision.DyadicMeshSafe segment
      zeroEndpoint oneEndpoint
      (ownerAtStart segment owner)
      depth diameter positive)
    (value : Preparation.Terminal.AcquiredDyadic segment within owner diameter positive) (same : value.depth
      = depth) :
    value = (AcquiredDyadic.acquire segment within owner diameter positive depth depth
      safe).val := by
  apply acquired_eq_of_depth segment within value
  have selected := (AcquiredDyadic.acquire segment within owner diameter positive depth
    depth safe).property
  exact same.trans (selected.elim id id).symm

/-- Read a checked dyadic attempt as either its exact requested-depth acquisition or the retained checker failure. -/
@[expose] def atDepth (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (depth : Nat)
    (saved : Checked segment within
      zeroEndpoint (ownerAtStart segment
      owner)
      (Subdivision.dyadicRequests depth
        zeroEndpoint oneEndpoint diameter
        positive)) :
    DepthResult segment within owner diameter positive depth := by
  rcases saved with ⟨saved, _same⟩
  cases saved with
  | declined failure => exact .declined failure
  | accepted retained =>
      exact .accepted (AcquiredDyadic.ofExecution depth _ rfl retained) rfl

/-- A successful shorter preferred-depth acquisition equals the original constructor's selected result. -/
theorem acquired_eq_preferred (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (preferred safeDepth : Nat)
    (safe : Subdivision.DyadicMeshSafe segment
      zeroEndpoint oneEndpoint
      (ownerAtStart segment owner)
      safeDepth diameter positive) (shorter : preferred < safeDepth)
    (value : Preparation.Terminal.AcquiredDyadic segment within owner diameter positive) (same : value.depth
      = preferred) :
    value = (AcquiredDyadic.acquire segment within owner diameter positive preferred
      safeDepth safe).val := by
  apply acquired_eq_of_depth segment within value
  apply same.trans
  symm
  unfold AcquiredDyadic.acquire
  simp only [if_pos shorter]
  cases found : TerminalAcquisition.attempt segment within
    zeroEndpoint (ownerAtStart segment
    owner)
      (Subdivision.dyadicRequests preferred
        zeroEndpoint oneEndpoint diameter
        positive) with
  | accepted retained => rfl
  | declined failure =>
      have success := value.success
      rw [same] at success
      change Subdivision.trySteps _ _ _ _ _ = some _ at success
      rw [failure] at success
      cases success

/-- When the preferred depth is not shorter, a successful safe-depth acquisition equals the original selected result. -/
theorem acquired_eq_without_preferred (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (preferred safeDepth : Nat)
    (safe : Subdivision.DyadicMeshSafe segment
      zeroEndpoint oneEndpoint
      (ownerAtStart segment owner)
      safeDepth diameter positive) (notShorter : ¬ preferred < safeDepth)
    (value : Preparation.Terminal.AcquiredDyadic segment within owner diameter positive) (same : value.depth
      = safeDepth) :
    value = (AcquiredDyadic.acquire segment within owner diameter positive preferred
      safeDepth safe).val := by
  apply acquired_eq_of_depth segment within value
  apply same.trans
  symm
  unfold AcquiredDyadic.acquire
  simp only [if_neg notShorter]
  cases found : TerminalAcquisition.attempt segment within
    zeroEndpoint (ownerAtStart segment
    owner)
      (Subdivision.dyadicRequests safeDepth
        zeroEndpoint oneEndpoint diameter
        positive) with
  | accepted retained => rfl
  | declined failure =>
      have success := value.success
      rw [same] at success
      change Subdivision.trySteps _ _ _ _ _ = some _ at success
      rw [failure] at success
      cases success

/-- After a proved preferred-depth rejection, a successful safe-depth acquisition equals the original selected fallback.
-/
theorem acquired_eq_after_decline (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (preferred safeDepth : Nat)
    (safe : Subdivision.DyadicMeshSafe segment
      zeroEndpoint oneEndpoint
      (ownerAtStart segment owner)
      safeDepth diameter positive) (shorter : preferred < safeDepth)
    (declined : Subdivision.tryDyadic segment within
      zeroEndpoint oneEndpoint
      (ownerAtStart segment owner)
      preferred diameter positive = none)
    (value : Preparation.Terminal.AcquiredDyadic segment within owner diameter positive) (same : value.depth
      = safeDepth) :
    value = (AcquiredDyadic.acquire segment within owner diameter positive preferred
      safeDepth safe).val := by
  apply acquired_eq_of_depth segment within value
  apply same.trans
  symm
  unfold AcquiredDyadic.acquire
  simp only [if_pos shorter]
  cases found : TerminalAcquisition.attempt segment within
    zeroEndpoint (ownerAtStart segment
    owner)
      (Subdivision.dyadicRequests preferred
        zeroEndpoint oneEndpoint diameter
        positive) with
  | accepted retained =>
      have success := TerminalAcquisition.Execution.success retained
      change Subdivision.trySteps _ _ _ _ _ = none at declined
      rw [declined] at success
      cases success
  | declined failure =>
      cases later : TerminalAcquisition.attempt segment within
        zeroEndpoint (ownerAtStart segment
        owner)
          (Subdivision.dyadicRequests safeDepth
            zeroEndpoint oneEndpoint
            diameter positive) with
      | accepted retained => rfl
      | declined failure =>
          have success := value.success
          rw [same] at success
          change Subdivision.trySteps _ _ _ _ _ = some _ at success
          rw [failure] at success
          cases success

end Purelib.RootIsolation.SquareRoot.Replay.TerminalAcquisitionReplay

end
