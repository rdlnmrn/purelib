module

meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.System.FilePath

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.RootIsolation.Newton.Search.Trace

import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
public import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackSampleReplay
public import scripts.checkpoint.RootRefinement
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.Newton.Search.Iteration
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic
import scripts.checkpoint.Integration
import scripts.checkpoint.RootState
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.Newton.Search

open Purelib.RootIsolation.SquareRoot.Clearance

open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance

open Purelib.RootIsolation.SquareRoot.Replay

open Purelib.Data (Json)
open scoped Purelib.Data.String
open Purelib.Data.Json (toJson)

public section

/-!
Disk-backed exact sample prefixes for the original quadratic track.  The
target index is retained in the result type, so a consumer can immediately
use the sample's source equation.  A finite miss retains the checked prefix,
the actual stopping trace and the unresolved total-refiner obligation.
The step paths intentionally match the earlier saved-root diagnostic format.
-/

namespace QuadraticSampleCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open IntegrationCheckpoint
open Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay (Coordinate Gaussian Box attempt)
open Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay (Track CheckedFirst)
open Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackSampleReplay
open Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay (Plan)

variable {parameter : Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay.Gaussian} {ambient :
  Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay.Box} (track :
  Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay.Track parameter ambient)

set_option genInjectivity false in
/-- The unresolved fallback obligation at a retained source-track cursor.

The index and original plan remain in the type, distinguishing absent source laws from a deferred finite replay. -/
inductive PendingFallback {index : Nat} (cursor : QuadraticTrackSampleReplay.Cursor track index) :
  QuadraticFallbackReplay.Plan track → Type
  /-- The checked-first plan supplies no equation for the original fallback. -/ | missingSourceLaw : PendingFallback
    cursor .checkedFirstOnly
  /-- A deferred fallback attempt retains its exact inconclusive replay data. -/ | deferred {nonzero equation}
      (pending : QuadraticFallbackCheckpoint.Pending cursor.state cursor.epsilon cursor.epsilon_positive) :
      PendingFallback cursor (.deferred nonzero equation)

constructive_injectivity PendingFallback

/-- Serialize the unresolved source law or deferred fallback evidence. -/
@[expose] def PendingFallback.report {index : Nat} {cursor : QuadraticTrackSampleReplay.Cursor track index} {plan :
  QuadraticFallbackReplay.Plan track} :
    PendingFallback track cursor plan → Json
  | .missingSourceLaw => Json.mkObj
      [("kind", toJson "original fallback history has no replay equation in this finite attempt")]
  | .deferred pending => pending.report cursor.state

/-- Replay the requested original fallback after a certified failed first attempt.

Success retains equality to the original refiner result; failure retains the plan-specific unresolved obligation. -/
@[expose] def runFallback (plan : QuadraticFallbackReplay.Plan track) {index : Nat} (cursor :
  QuadraticTrackSampleReplay.Cursor track index)
    (missed : QuadraticSampleReplay.attempt cursor.state cursor.epsilon = none)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    IO (Except (PendingFallback track cursor plan)
      { next : QuadraticSampleReplay.State parameter ambient //
        track.refine cursor.state cursor.epsilon cursor.epsilon_positive = next }) := by
  cases plan with
  | checkedFirstOnly => exact pure (.error .missingSourceLaw)
  | deferred nonzero equation => exact do
      let result ← QuadraticFallbackCheckpoint.run cursor.state cursor.epsilon cursor.epsilon_positive
        ⟨control.savedOnly, pure ()⟩ directory
      match result with
      | .error pending => return .error (.deferred pending)
      | .ok accepted =>
          return .ok ⟨QuadraticFallbackReplay.fastState accepted.val,
            (equation cursor.state cursor.epsilon cursor.epsilon_positive).trans
              (QuadraticFallbackReplay.deferred_refine nonzero track.initial cursor.state
                cursor.epsilon cursor.epsilon_positive missed accepted.val accepted.property)⟩

set_option genInjectivity false in
/-- An inconclusive sample attempt before the requested target index.

The record retains the exact cursor, finite search trace, failed result and unresolved original fallback. -/
structure Stopped (target : Nat) where
  /-- The index of the last completed source-track state. -/ index : Nat
  /-- The completed index is strictly before the requested target. -/ beforeTarget : index < target
  /-- The original source-track cursor at the completed index. -/ cursor : QuadraticTrackSampleReplay.Cursor track index
  /-- The inconclusive finite sample attempt at that cursor. -/ failure : QuadraticTrackSampleReplay.Inconclusive cursor
  /-- The completed search trace with its original parameter, state, tolerance and proposal center. -/ trace :
    Trace.Finished
    (QuadraticAxisElimination.quadraticAxisElimination parameter)
    cursor.state.raw cursor.epsilon
    (Owner.quadraticAxisClearances parameter)
    ⟨(cursor.state.box.xLower + cursor.state.box.xUpper) / 2,
      (cursor.state.box.yLower + cursor.state.box.yUpper) / 2⟩
  /-- The retained search trace returned no accepted proposal. -/ traceMiss : trace.value = none
  /-- The original fallback plan attempted after the finite miss. -/ plan : QuadraticFallbackReplay.Plan track
  /-- The unresolved obligation for that exact cursor and fallback plan. -/ fallback : PendingFallback track cursor plan

constructive_injectivity Stopped

/-- Serialize the retained cursor, search budget, failed trace and fallback obligation. -/
@[expose] def Stopped.report {target : Nat} (stopped : Stopped track target) : Json :=
  Json.mkObj
    [("kind", toJson "inconclusive finite sample replay; total fallback unresolved, not non-certifiability"),
     ("targetIndex", toJson target), ("completedIndex", toJson stopped.index),
     ("refiner", toJson "original track; checked first attempt"),
     ("epsilon", toJson (fractionData stopped.failure.epsilon)),
     ("budget", toJson stopped.failure.proposalBudget),
     ("state", toJson (RootStateCheckpoint.capture stopped.cursor.state)),
     ("trace", RootRefinementCheckpoint.finishedReport _ _ _ _ _ stopped.trace),
     ("fallback", stopped.fallback.report track)]

/-- Restore an exact source-track prefix up to the requested target index.

Each step reuses checked saved proposals or the original fallback; inconclusivity retains the complete stopping evidence
and original state equation. -/
@[expose] def runFrom (plan : IO (QuadraticFallbackReplay.Plan track)) (control : RootRefinementCheckpoint.Control)
  (directory : System.FilePath)
    (target : Nat) : (remaining index : Nat) → (bound : index + remaining = target) →
      (cursor : QuadraticTrackSampleReplay.Cursor track index) → cursor.state = CoherentRoot.state track index →
      m (Except (Stopped track target) (QuadraticTrackSampleReplay.Cursor track target))
  | 0, index, bound, cursor, _ => do
      have same : index = target := by omega
      return .ok (same ▸ cursor)
  | remaining + 1, index, bound, cursor, stateEq => do
      let epsilon := cursor.epsilon
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"step-{index}-input.json"))))
        (RootStateCheckpoint.boxData cursor.state.box, fractionData epsilon)
      profile directory s!"BEGIN checked root step {index + 1}"
      let trace ← RootRefinementCheckpoint.run
        (QuadraticAxisElimination.quadraticAxisElimination parameter)
        cursor.state.raw epsilon
        (Owner.quadraticAxisClearances parameter)
        (.direct _ _)
        control ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"step-{index + 1}-trace"))))
      match found : trace.value with
      | none =>
          have missed : QuadraticSampleReplay.attempt cursor.state cursor.epsilon = none := trace.equation.trans found
          profile directory s!"BEGIN original fallback at root step {index + 1}"
          let fallbackPlan ← plan
          match ← runFallback track fallbackPlan cursor missed control ((Purelib.System.FilePath.join directory
            (System.FilePath.mk (s!"step-{index + 1}-fallback")))) with
          | .error pending =>
              let failure : QuadraticTrackSampleReplay.Inconclusive cursor :=
                ⟨cursor, rfl, index, rfl, epsilon, rfl, 6, rfl, missed⟩
              let stopped : Stopped track target :=
                ⟨index, by omega, cursor, failure, trace, found, fallbackPlan, pending⟩
              saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive.json"))))
                (stopped.report track)
              saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("reuse-counts.json")))) (←
                RootRefinementCheckpoint.Execution.counts)
              return .error stopped
          | .ok accepted =>
              let next := cursor.ofRefinement accepted.val stateEq accepted.property
              saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
                (s!"step-{index + 1}-output.json")))) (RootStateCheckpoint.capture next.state)
              profile directory
                s!"END original fallback at root step {index + 1}; complete source-state equation retained"
              runFrom plan control directory target remaining (index + 1) (by omega) next
                (cursor.ofRefinement_state_eq accepted.val stateEq accepted.property)
      | some accepted =>
          let next := cursor.ofAccepted accepted (trace.equation.trans found)
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"step-{index + 1}-output.json"))))
            (RootStateCheckpoint.capture next.state)
          profile directory s!"END checked root step {index + 1}; original sample-box equation retained"
          runFrom plan control directory target remaining (index + 1) (by omega) next
            (cursor.ofAccepted_state_eq accepted (trace.equation.trans found))

/-- Start from the source's actual initial state; no isolation or original refiner runs. Every expensive proposal is
handled by the shared checked checkpoint driver, including saved-only and interrupted-write modes. -/
@[expose] def run (ready : QuadraticTrackReplay.CheckedFirst track) (plan : IO (QuadraticFallbackReplay.Plan track))
  (control : RootRefinementCheckpoint.Control)
    (directory : System.FilePath) (target : Nat) :
    m (Except (Stopped track target) (QuadraticTrackSampleReplay.Cursor track target)) := do
  IO.FS.createDirAll directory
  let result ← runFrom track plan control directory target target 0 (by omega)
    (QuadraticTrackSampleReplay.first track ready track.initial rfl) rfl
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("reuse-counts.json")))) (←
    RootRefinementCheckpoint.Execution.counts)
  return result

end QuadraticSampleCheckpoint
