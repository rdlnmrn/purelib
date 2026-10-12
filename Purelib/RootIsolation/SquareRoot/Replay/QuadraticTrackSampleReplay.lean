module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.RootIsolation.Refinement.Basic

import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.CoherentRoot
public import Purelib.Riemann.Transport.PreparedCenterReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay
public import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic

open Purelib

open Purelib.RootIsolation

public section

/-!
Checked finite sample prefixes indexed by the actual original quadratic
track.  Only its successful-first-attempt law is used; its total fallback
is never replaced by a newly selected refiner.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackSampleReplay

open QuadraticSampleReplay (Coordinate Gaussian Box State attempt)
open QuadraticTrackReplay (Track CheckedFirst)
open Purelib.Riemann.Integration

/-- A successful first attempt from a same-box state equals the retained ready track's refinement. -/
theorem refine_eq_of_same_box_attempt {parameter : Gaussian} {ambient : Box}
    (track : Track parameter ambient) (ready : CheckedFirst track)
    (current restored : State parameter ambient) (same : restored.box = current.box)
    (epsilon : Coordinate) (positive : 0 < epsilon)
    (accepted : Refinement restored.raw epsilon)
    (found : attempt restored epsilon = some accepted) :
    track.refine current epsilon positive = accepted.state := by
  have agree := SquareRoot.Replay.QuadraticSampleReplay.attempt_eq_of_box_eq restored current same epsilon
  rw [found] at agree
  cases original : attempt current epsilon with
  | none => simp only [original, Option.map] at agree; cases agree
  | some result =>
      simp only [original, Option.map, -eq_self] at agree
      have same := Option.some.inj agree
      exact (ready current epsilon positive result original).trans same.symm

set_option genInjectivity false in
/-- The source track is only a proof index.  Runtime data are the restored
finite state and the cached original error scale. -/
structure Cursor {parameter : Gaussian} {ambient : Box}
    (track : Track parameter ambient) (index : Nat) where
  /-- The actual finite winding-one state retained by this replay cursor. -/ state : State parameter ambient
  /-- The cached original track scale at the retained index. -/ scale : Coordinate
  /-- The cached scale equals the original track's scale at this index. -/ scale_eq : scale =
    Riemann.RootContinuation.CoherentRoot.scale track
  /-- The retained state box equals the original track's box at this index. -/ box_eq : state.box =
    (Riemann.RootContinuation.CoherentRoot.state track index).box
  /-- The original track agrees with every successful bounded first attempt. -/ checkedFirst : CheckedFirst track

constructive_injectivity Cursor

/-- Initialize a replay cursor with the original track state, scale and checked first-attempt certificate. -/
@[expose] def first {parameter : Gaussian} {ambient : Box} (track : Track parameter ambient)
    (ready : CheckedFirst track) (restored : State parameter ambient)
    (same : restored.box = track.initial.box) : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track 0 where
  state := restored
  scale := restored.box.diagonalSq
  scale_eq := by unfold Riemann.RootContinuation.CoherentRoot.scale; rw [same]
  box_eq := same
  checkedFirst := ready

/-- Compute the next replay accuracy from the cursor's retained original scale. -/
@[expose] def Cursor.epsilon {parameter : Gaussian} {ambient : Box} {track : Track parameter ambient}
    {index : Nat} (cursor : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index) : Coordinate :=
  Data.Rat.Bounds.AccuracyRadius.accuracyRadius (Approximation.Rational.Geometric.Basic.quarterRadius cursor.scale
    (index + 1))

/-- The computed replay accuracy equals the original track's prescribed next accuracy. -/
theorem Cursor.epsilon_eq {parameter : Gaussian} {ambient : Box} {track : Track parameter ambient}
    {index : Nat} (cursor : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index) :
    cursor.epsilon = Data.Rat.Bounds.AccuracyRadius.accuracyRadius (Riemann.RootContinuation.CoherentRoot.stepTarget
      track index) := by
  unfold SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor.epsilon Riemann.RootContinuation.CoherentRoot.stepTarget
  rw [cursor.scale_eq]

/-- The next replay accuracy is positive. -/
theorem Cursor.epsilon_positive {parameter : Gaussian} {ambient : Box} {track : Track parameter ambient}
    {index : Nat} (cursor : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index) : 0 < cursor.epsilon := by
  rw [cursor.epsilon_eq]
  exact Data.Rat.Bounds.AccuracyRadius.accuracyRadius_pos (Riemann.RootContinuation.CoherentRoot.stepTarget_positive _
    _)

set_option genInjectivity false in
/-- This certifies the failed bounded attempt, not failure of the original
total track.  The successful prefix, request and remaining fallback are retained. -/
structure Inconclusive {parameter : Gaussian} {ambient : Box} {track : Track parameter ambient}
    {index : Nat} (cursor : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index) where
  /-- The unchanged cursor retained after the unsuccessful finite attempt. -/ retained :
    SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index
  /-- The retained cursor is exactly the supplied current cursor. -/ retained_eq : retained = cursor
  /-- The original track index at which the finite attempt stopped. -/ atIndex : Nat
  /-- The stopping index equals the supplied cursor's retained index. -/ atIndex_eq : atIndex = index
  /-- The actual accuracy requested by the unsuccessful attempt. -/ epsilon : Coordinate
  /-- The retained request equals the current cursor's prescribed next accuracy. -/ epsilon_eq : epsilon =
    cursor.epsilon
  /-- The exact finite proposal budget used by the failed attempt. -/ proposalBudget : Nat
  /-- The retained proposal budget equals the original first-attempt budget of six. -/ proposalBudget_eq :
    proposalBudget = 6
  /-- The original bounded attempt at the retained state and accuracy returned no refinement. -/ missed : attempt
    cursor.state epsilon = none

constructive_injectivity Inconclusive

/-- Advance the cursor using the actual accepted first-attempt refinement.

Retain its original next-state equation and the track's next scale without replacing the total refiner. -/
@[expose] def Cursor.ofAccepted {parameter : Gaussian} {ambient : Box} {track : Track parameter ambient}
    {index : Nat} (cursor : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index)
    (accepted : Refinement cursor.state.raw cursor.epsilon)
    (found : attempt cursor.state cursor.epsilon = some accepted) : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor
      track (index + 1) :=
  have same : accepted.state = Riemann.RootContinuation.CoherentRoot.state track (index + 1) := by
    rw [Riemann.RootContinuation.CoherentRoot.state]
    have refined := SquareRoot.Replay.QuadraticTrackSampleReplay.refine_eq_of_same_box_attempt track cursor.checkedFirst
      _ cursor.state
      cursor.box_eq cursor.epsilon cursor.epsilon_positive accepted found
    simpa only [cursor.epsilon_eq] using refined.symm
  ⟨accepted.state, cursor.scale, cursor.scale_eq, congrArg (fun state => state.box) same,
    cursor.checkedFirst⟩

/-- The cursor built from an accepted first attempt retains its exact returned state. -/
theorem Cursor.ofAccepted_state_eq {parameter : Gaussian} {ambient : Box} {track : Track parameter ambient}
    {index : Nat} (cursor : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index)
    (accepted : Refinement cursor.state.raw cursor.epsilon)
    (found : attempt cursor.state cursor.epsilon = some accepted) :
    (cursor.ofAccepted accepted found).state = Riemann.RootContinuation.CoherentRoot.state track (index + 1) := by
  change accepted.state = _
  rw [Riemann.RootContinuation.CoherentRoot.state]
  have refined := SquareRoot.Replay.QuadraticTrackSampleReplay.refine_eq_of_same_box_attempt track cursor.checkedFirst _
    cursor.state
    cursor.box_eq cursor.epsilon cursor.epsilon_positive accepted found
  simpa only [cursor.epsilon_eq] using refined.symm

/-- A checked fallback must identify the original next state, including its
clearance data. The same cursor then continues through the ordinary sampler. -/
@[expose] def Cursor.ofRefinement {parameter : Gaussian} {ambient : Box} {track : Track parameter ambient}
    {index : Nat} (cursor : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index) (next : State parameter
      ambient)
    (current_eq : cursor.state = Riemann.RootContinuation.CoherentRoot.state track index)
    (same : track.refine cursor.state cursor.epsilon cursor.epsilon_positive = next) :
    SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track (index + 1) :=
  have original : next = Riemann.RootContinuation.CoherentRoot.state track (index + 1) := by
    rw [Riemann.RootContinuation.CoherentRoot.state]
    simpa only [current_eq, cursor.epsilon_eq] using same.symm
  ⟨next, cursor.scale, cursor.scale_eq, congrArg (fun state => state.box) original,
    cursor.checkedFirst⟩

/-- The cursor built from a certified original refinement retains that refinement's exact state. -/
theorem Cursor.ofRefinement_state_eq {parameter : Gaussian} {ambient : Box} {track : Track parameter ambient}
    {index : Nat} (cursor : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index) (next : State parameter
      ambient)
    (current_eq : cursor.state = Riemann.RootContinuation.CoherentRoot.state track index)
    (same : track.refine cursor.state cursor.epsilon cursor.epsilon_positive = next) :
    (cursor.ofRefinement next current_eq same).state = Riemann.RootContinuation.CoherentRoot.state track (index + 1) :=
      by
  change next = _
  rw [Riemann.RootContinuation.CoherentRoot.state]
  simpa only [current_eq, cursor.epsilon_eq] using same.symm

/-- Try the original bounded first attempt at the cursor's next accuracy.

Return the next cursor on success, or retain the current cursor and exact failed finite attempt on failure. -/
@[expose] def advance {parameter : Gaussian} {ambient : Box} {track : Track parameter ambient}
    {index : Nat} (cursor : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track index) :
    Except (SquareRoot.Replay.QuadraticTrackSampleReplay.Inconclusive cursor)
      (SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor track (index + 1)) :=
  match found : attempt cursor.state cursor.epsilon with
  | none => .error ⟨cursor, rfl, index, rfl, cursor.epsilon, rfl, 6, rfl, found⟩
  | some accepted => .ok (cursor.ofAccepted accepted found)

/-- Read the exact center sample from the cursor's retained box and original track index. -/
@[expose] def centerSample {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
    (edge : Riemann.Integration.PreparedConstantModels.PreparedEdge curve differential)
    (cursor : SquareRoot.Replay.QuadraticTrackSampleReplay.Cursor (edge.directQueryOwner 0 edge.baseInside).track
      (Riemann.Transport.PreparedCenterReplay.metadata edge).sampleIndex) :
        Riemann.Transport.PreparedCenterReplay.Sample edge :=
  Riemann.Transport.PreparedCenterReplay.Sample.ofBox edge cursor.state.box cursor.box_eq

end Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackSampleReplay

end
