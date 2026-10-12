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

attribute [local irreducible] Riemann.Branches.PreparedSheetContinuation.advanceCached
  Riemann.Branches.PreparedSheetContinuation.retainedAtReserve

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)

/-- The original checked acquisition attempt for the exact initial owner and finite request list. -/
abbrev Outcome (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) (requests : List
      Riemann.Branches.PreparedSheetContinuation.StepRequest) :=
  SquareRoot.Preparation.Terminal.TerminalAcquisition.Attempt segment within current owner requests

/-- A retained acquisition outcome with equality to the original finite execution. -/
abbrev Checked (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) (requests : List
      Riemann.Branches.PreparedSheetContinuation.StepRequest) :=
  {value : SquareRoot.Replay.TerminalAcquisitionReplay.Outcome segment within current owner requests //
    value = SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt segment within current owner requests}

/-- Restore the empty-request execution with its original endpoint and owner. -/
@[expose] def stop (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) :
    SquareRoot.Replay.TerminalAcquisitionReplay.Checked segment within current owner [] :=
  ⟨SquareRoot.Preparation.Terminal.TerminalAcquisition.Attempt.accepted
    (SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution.mk (.stop current owner) rfl current rfl owner
    HEq.rfl), rfl⟩

/-- Restore a declined attempt whose first requested endpoint precedes the current parameter. -/
@[expose] def unordered (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : Riemann.Branches.PreparedSheetContinuation.StepRequest) (requests : List
      Riemann.Branches.PreparedSheetContinuation.StepRequest)
    (miss : ¬ current.parameter ≤ request.endpoint.parameter) :
    SquareRoot.Replay.TerminalAcquisitionReplay.Checked segment within current owner (request :: requests) := by
  refine ⟨SquareRoot.Preparation.Terminal.TerminalAcquisition.Attempt.declined ?_, ?_⟩
  · simp only [Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps, dif_neg miss, -eq_self]
    rfl
  · dsimp only [SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt]
    simp only [dif_neg miss, -eq_self]
    rfl

/-- Restore a declined attempt whose first variation bound fails the cached source's clearance test. -/
@[expose] def tooLarge (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : Riemann.Branches.PreparedSheetContinuation.StepRequest) (requests : List
      Riemann.Branches.PreparedSheetContinuation.StepRequest)
    (cached : Riemann.Branches.PreparedSheetContinuation.CachedSource segment current owner request)
    (ordered : current.parameter ≤ request.endpoint.parameter)
    (miss : ¬ Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter <
      cached.preparedOwner.track.initial.clearance.bound) :
    SquareRoot.Replay.TerminalAcquisitionReplay.Checked segment within current owner (request :: requests) := by
  have same := cached.eq_canonical
  cases same
  refine ⟨SquareRoot.Preparation.Terminal.TerminalAcquisition.Attempt.declined ?_, ?_⟩
  · rw [Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps, dif_pos ordered, dif_neg miss]
  · dsimp only [SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt]
    simp only [dif_pos ordered, dif_neg miss, -eq_self]
    rfl

/-- Prepend one checked cached-source step to an exactly restored tail execution.

The successor owner must equal the original cached advance; both accepted and declined tails preserve the original full
execution. -/
@[expose] def prepend (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : Riemann.Branches.PreparedSheetContinuation.StepRequest) (requests : List
      Riemann.Branches.PreparedSheetContinuation.StepRequest)
    (cached : Riemann.Branches.PreparedSheetContinuation.CachedSource segment current owner request)
    (ordered : current.parameter ≤ request.endpoint.parameter)
    (small : Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter
      <
      cached.preparedOwner.track.initial.clearance.bound)
    (next : Owner (polynomial.eval (segment.pointAt request.endpoint.parameter)))
    (nextEq : next = Riemann.Branches.PreparedSheetContinuation.advanceCached segment within current owner request
      cached small)
    (tail : SquareRoot.Replay.TerminalAcquisitionReplay.Checked segment within request.endpoint next requests) :
    SquareRoot.Replay.TerminalAcquisitionReplay.Checked segment within current owner (request :: requests) := by
  cases nextEq
  have canonicalSmall : Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
    request.endpoint.parameter <
      (Riemann.Branches.PreparedSheetContinuation.prepared segment current owner request).track.initial.clearance.bound
        := by
    rw [← cached.preparedOwner_eq]
    exact small
  have same := cached.eq_canonical
  cases same
  rcases tail with ⟨tail, tailEq⟩
  cases tail with
  | declined failure =>
      refine ⟨SquareRoot.Preparation.Terminal.TerminalAcquisition.Attempt.declined ?_, ?_⟩
      · rw [Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps, dif_pos ordered, dif_pos small]
        dsimp only
        rw [failure]
      · dsimp only [SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt]
        simp only [dif_pos ordered, dif_pos small, ← tailEq, -eq_self]
        rfl
  | accepted rest =>
      refine ⟨SquareRoot.Preparation.Terminal.TerminalAcquisition.Attempt.accepted
        (SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution.mk
        (Riemann.Branches.PreparedSheetContinuation.Subdivision.nextCached segment within current owner request
          (Riemann.Branches.PreparedSheetContinuation.CachedSource.canonical segment current owner request) ordered
            small canonicalSmall (SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution.subdivision rest))
        ?_ (SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution.endpoint rest)
          ((Riemann.Branches.PreparedSheetContinuation.Subdivision.nextCached_endpoint ..).trans
          (SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution.endpoint_eq rest))
        (SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution.terminalOwner rest) ?_), ?_⟩
      · rw [Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps, dif_pos ordered, dif_pos small]
        dsimp only
        rw [(SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution.success rest)]
      · exact (SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution.terminalOwner_heq rest).trans
          (SquareRoot.Preparation.Terminal.TerminalAcquisition.castOwner_terminal_heq
          (Riemann.Branches.PreparedSheetContinuation.advanceCached_eq_advance segment within current owner request
            (Riemann.Branches.PreparedSheetContinuation.CachedSource.canonical segment current owner request) small
              canonicalSmall)
          (SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution.subdivision rest)).symm
      · dsimp only [SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt]
        simp only [dif_pos ordered, dif_pos small, ← tailEq, -eq_self]
        rfl

/-- Successful acquisitions at one depth have the same entire retained data,
including their request list and terminal owner. -/
theorem acquired_eq_of_depth {owner : Owner (polynomial.eval start)} {diameter : Fraction.Rational}
    {positive : 0 < diameter}
    (first second : SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner diameter positive)
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
    SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner diameter positive) (same : value.depth = depth)
  /-- The original dyadic checker returned no subdivision at the exact requested depth. -/ | declined (failure :
    Riemann.Branches.PreparedSheetContinuation.Subdivision.tryDyadic segment within
    Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
      (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner) depth diameter positive = none)

constructive_injectivity DepthResult

/-- A successful acquisition at the safe depth equals the original safe-depth constructor's complete retained result. -/
theorem acquired_eq_safe (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (depth : Nat)
    (safe : Riemann.Branches.PreparedSheetContinuation.Subdivision.DyadicMeshSafe segment
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
      (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner)
      depth diameter positive)
    (value : SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner diameter positive) (same : value.depth
      = depth) :
    value = (SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire segment within owner diameter positive depth depth
      safe).val := by
  apply SquareRoot.Replay.TerminalAcquisitionReplay.acquired_eq_of_depth segment within value
  have selected := (SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire segment within owner diameter positive depth
    depth safe).property
  exact same.trans (selected.elim id id).symm

/-- Read a checked dyadic attempt as either its exact requested-depth acquisition or the retained checker failure. -/
@[expose] def atDepth (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (depth : Nat)
    (saved : SquareRoot.Replay.TerminalAcquisitionReplay.Checked segment within
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment
      owner)
      (Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint diameter
        positive)) :
    SquareRoot.Replay.TerminalAcquisitionReplay.DepthResult segment within owner diameter positive depth := by
  rcases saved with ⟨saved, _same⟩
  cases saved with
  | declined failure => exact .declined failure
  | accepted retained =>
      exact .accepted (SquareRoot.Preparation.Terminal.AcquiredDyadic.ofExecution depth _ rfl retained) rfl

/-- A successful shorter preferred-depth acquisition equals the original constructor's selected result. -/
theorem acquired_eq_preferred (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (preferred safeDepth : Nat)
    (safe : Riemann.Branches.PreparedSheetContinuation.Subdivision.DyadicMeshSafe segment
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
      (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner)
      safeDepth diameter positive) (shorter : preferred < safeDepth)
    (value : SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner diameter positive) (same : value.depth
      = preferred) :
    value = (SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire segment within owner diameter positive preferred
      safeDepth safe).val := by
  apply SquareRoot.Replay.TerminalAcquisitionReplay.acquired_eq_of_depth segment within value
  apply same.trans
  symm
  unfold SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire
  simp only [if_pos shorter]
  cases found : SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt segment within
    Riemann.Paths.PreparedClearPathModels.zeroEndpoint (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment
    owner)
      (Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicRequests preferred
        Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint diameter
        positive) with
  | accepted retained => rfl
  | declined failure =>
      have success := value.success
      rw [same] at success
      change Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps _ _ _ _ _ = some _ at success
      rw [failure] at success
      cases success

/-- When the preferred depth is not shorter, a successful safe-depth acquisition equals the original selected result. -/
theorem acquired_eq_without_preferred (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (preferred safeDepth : Nat)
    (safe : Riemann.Branches.PreparedSheetContinuation.Subdivision.DyadicMeshSafe segment
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
      (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner)
      safeDepth diameter positive) (notShorter : ¬ preferred < safeDepth)
    (value : SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner diameter positive) (same : value.depth
      = safeDepth) :
    value = (SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire segment within owner diameter positive preferred
      safeDepth safe).val := by
  apply SquareRoot.Replay.TerminalAcquisitionReplay.acquired_eq_of_depth segment within value
  apply same.trans
  symm
  unfold SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire
  simp only [if_neg notShorter]
  cases found : SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt segment within
    Riemann.Paths.PreparedClearPathModels.zeroEndpoint (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment
    owner)
      (Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicRequests safeDepth
        Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint diameter
        positive) with
  | accepted retained => rfl
  | declined failure =>
      have success := value.success
      rw [same] at success
      change Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps _ _ _ _ _ = some _ at success
      rw [failure] at success
      cases success

/-- After a proved preferred-depth rejection, a successful safe-depth acquisition equals the original selected fallback.
-/
theorem acquired_eq_after_decline (owner : Owner (polynomial.eval start)) (diameter : Fraction.Rational)
    (positive : 0 < diameter) (preferred safeDepth : Nat)
    (safe : Riemann.Branches.PreparedSheetContinuation.Subdivision.DyadicMeshSafe segment
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
      (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner)
      safeDepth diameter positive) (shorter : preferred < safeDepth)
    (declined : Riemann.Branches.PreparedSheetContinuation.Subdivision.tryDyadic segment within
      Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
      (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment owner)
      preferred diameter positive = none)
    (value : SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner diameter positive) (same : value.depth
      = safeDepth) :
    value = (SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire segment within owner diameter positive preferred
      safeDepth safe).val := by
  apply SquareRoot.Replay.TerminalAcquisitionReplay.acquired_eq_of_depth segment within value
  apply same.trans
  symm
  unfold SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire
  simp only [if_pos shorter]
  cases found : SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt segment within
    Riemann.Paths.PreparedClearPathModels.zeroEndpoint (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment
    owner)
      (Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicRequests preferred
        Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint diameter
        positive) with
  | accepted retained =>
      have success := SquareRoot.Preparation.Terminal.TerminalAcquisition.Execution.success retained
      change Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps _ _ _ _ _ = none at declined
      rw [declined] at success
      cases success
  | declined failure =>
      cases later : SquareRoot.Preparation.Terminal.TerminalAcquisition.attempt segment within
        Riemann.Paths.PreparedClearPathModels.zeroEndpoint (Riemann.Paths.PreparedClearPathModels.ownerAtStart segment
        owner)
          (Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicRequests safeDepth
            Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
            diameter positive) with
      | accepted retained => rfl
      | declined failure =>
          have success := value.success
          rw [same] at success
          change Riemann.Branches.PreparedSheetContinuation.Subdivision.trySteps _ _ _ _ _ = some _ at success
          rw [failure] at success
          cases success

end Purelib.RootIsolation.SquareRoot.Replay.TerminalAcquisitionReplay

end
