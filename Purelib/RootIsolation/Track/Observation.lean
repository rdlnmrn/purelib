module

public import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Refinement.Basic
public import Purelib.RootIsolation.State.WindingOne.Raw
public import Purelib.RootIsolation.State.WindingOne.Comparison
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Computation.Query.Boundary
import Purelib.Data.Rat.Fraction
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained winding-track refinement requests

A request carries the actual original current state and a positive radius.
Its identity certificate permits executable query comparison even when an
owner contains functions. The reply retains the exact refinement output;
replay and downstream projections never invoke the refinement callback.
-/

public section

namespace Purelib.RootIsolation.Track

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.Computation.Query

namespace Observation

variable {p : CoefficientPolynomial} {ambient : Box}

/-- An exact successful state action for the original track, current state and positive radius.

This is the retained success value checked by `receive`. The action may read
completed checkpoints; its state equality still identifies the same original
track refinement rather than a replacement policy or merely an accurate box.
-/
abbrev Handler (m : Type → Type) (track : Basic.WindingOneTrack p ambient) :=
  (current : WindingOneState p ambient) → (epsilon : Fraction.Rational) → (positive : 0 < epsilon) →
    m { state : WindingOneState p ambient // state = track.refine current epsilon positive }

set_option genInjectivity false in
/-- The actual retained current state and positive radius of an original winding-track refinement. -/
structure Question (origin : WindingOneState p ambient) where
  /-- The same original current state, with identity rather than a replacement owner or runtime identifier. -/ current :
    {state : WindingOneState p ambient // state = origin}
  /-- The positive original track-radius request. -/ epsilon : Fraction.Rational
  /-- The request satisfies the track's required strict positivity. -/ positive : 0 < epsilon

namespace Question

/-- Request a radius from the exact original current state. -/
@[expose] def ofCurrent (origin : WindingOneState p ambient) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Question origin := ⟨⟨origin, rfl⟩, epsilon, positive⟩

/-- Request a radius using an already retained equal current state, without reconstructing its winding certificate. -/
@[expose] def ofRetained {origin : WindingOneState p ambient}
    (current : {state : WindingOneState p ambient // state = origin})
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) : Question origin := ⟨current, epsilon, positive⟩

/-- Compare the radius and use the supplied original-state identities to compare retained current owners. -/
instance {origin : WindingOneState p ambient} : DecidableEq (Question origin) := fun left right =>
  if same : left.epsilon = right.epsilon then .isTrue (by
    cases left with
    | mk left epsilon positive =>
        cases right with
        | mk right other otherPositive =>
            cases same
            cases left with
            | mk current currentEq =>
                cases right with
                | mk second secondEq =>
                    cases currentEq
                    cases secondEq
                    rfl)
  else .isFalse (fun equal => same (congrArg Question.epsilon equal))

end Question

set_option genInjectivity false in
/-- A cached original refinement output, indexed by the same track and original current state. -/
structure Reply (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient) where
  /-- The complete actual request supplied to the refinement callback. -/ question : Question origin
  /-- The actual computed winding-one state, retained once. -/ state : WindingOneState p ambient
  /-- The reply is the same original callback's output at this exact current state and radius. -/ stateEq :
    state = track.refine question.current.val question.epsilon question.positive

namespace Reply

/-- The cached refinement state preserves containment in the same original current box. -/
theorem nested {track : Basic.WindingOneTrack p ambient} {origin : WindingOneState p ambient}
    (reply : Reply track origin) : reply.state.box.Refines reply.question.current.val.box := by
  rewrite [reply.stateEq]
  exact track.nested reply.question.current.val reply.question.epsilon reply.question.positive

/-- The cached refinement state is strictly inside the same original current box. -/
theorem strict {track : Basic.WindingOneTrack p ambient} {origin : WindingOneState p ambient}
    (reply : Reply track origin) : reply.state.box.StrictInterior reply.question.current.val.box := by
  rewrite [reply.stateEq]
  exact track.strict reply.question.current.val reply.question.epsilon reply.question.positive

/-- The same cached refinement meets its actual retained request's squared-diagonal bound. -/
theorem accurate {track : Basic.WindingOneTrack p ambient} {origin : WindingOneState p ambient}
    (reply : Reply track origin) : reply.state.box.diagonalSq ≤ reply.question.epsilon ^ 2 := by
  rewrite [reply.stateEq]
  exact track.accurate reply.question.current.val reply.question.epsilon reply.question.positive

end Reply

set_option genInjectivity false in
/-- The supplied refinement reply belongs to a different original request. -/
structure Mismatch (origin : WindingOneState p ambient) where
  /-- The complete original request. -/ expected : Question origin
  /-- The different request retained in the actual reply. -/ reported : Question origin
  /-- The reply violates request equality. -/ different : reported ≠ expected

/-- Execute the original track callback once and retain its actual state and exact request. -/
def answer (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) : Reply track origin :=
  let state := track.refine question.current.val question.epsilon question.positive
  ⟨question, state, rfl⟩

/-- The evaluator receipt retains its exact request and same original callback output. -/
private theorem answer_eq_spec (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) :
    answer track origin question =
      ⟨question, track.refine question.current.val question.epsilon question.positive, rfl⟩ := rfl

/-- The original evaluator returns the retained request and exact original refinement output. -/
theorem answer_eq (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) :
    answer track origin question =
      ⟨question, track.refine question.current.val question.epsilon question.positive, rfl⟩ :=
  answer_eq_spec track origin question

/-- Check a supplied refinement receipt and project its same cached state to the exact requested operation. -/
def receive (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) (reply : Reply track origin) :
    Except (Mismatch origin) {state : WindingOneState p ambient //
      state = track.refine question.current.val question.epsilon question.positive} :=
  if same : reply.question = question then
    have stateEq : reply.state = track.refine question.current.val question.epsilon question.positive := by
      cases same
      exact reply.stateEq
    .ok ⟨reply.state, stateEq⟩
  else .error ⟨question, reply.question, same⟩

/-- Consuming an actual original callback receipt preserves its same computed state and identity. -/
private theorem receive_answer_spec (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) :
    receive track origin question (answer track origin question) =
      .ok ⟨track.refine question.current.val question.epsilon question.positive, rfl⟩ := by
  unfold receive
  rewrite [dif_pos (show (answer track origin question).question = question from rfl)]
  rfl

/-- An original callback receipt is accepted with the exact same cached refinement state. -/
theorem receive_answer (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) :
    receive track origin question (answer track origin question) =
      .ok ⟨track.refine question.current.val question.epsilon question.positive, rfl⟩ :=
  receive_answer_spec track origin question

/-- Display the actual track-refinement request and consume only its retained output certificate. -/
def request (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) :
    Protocol (Question origin) (Reply track origin) (Except (Mismatch origin)
      {state : WindingOneState p ambient //
        state = track.refine question.current.val question.epsilon question.positive}) :=
  (Protocol.query question).map (receive track origin question)

/-- The canonical refinement reply returns precisely the original callback's computed state. -/
private theorem request_value_spec (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) :
    ((request track origin question).run (answer track origin)).value =
      .ok ⟨track.refine question.current.val question.epsilon question.positive, rfl⟩ := by
  change receive track origin question (answer track origin question) = _
  unfold receive
  rewrite [dif_pos (show (answer track origin question).question = question from rfl)]
  rfl

/-- The displayed request preserves the exact original callback result for every original winding track. -/
theorem request_value (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) :
    ((request track origin question).run (answer track origin)).value =
      .ok ⟨track.refine question.current.val question.epsilon question.positive, rfl⟩ :=
  request_value_spec track origin question

/-- The complete refinement execution contains the original state and exactly its actual request and retained reply. -/
theorem request_execution (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) :
    (request track origin question).run (answer track origin) =
      ⟨.ok ⟨track.refine question.current.val question.epsilon question.positive, rfl⟩,
        [⟨question, answer track origin question⟩]⟩ :=
  Basic.Execution.ext (request_value track origin question) (Protocol.map_run_trace _ _ _)

/-- Replay consumes the cached state and invokes no original refinement callback. -/
theorem request_replay (track : Basic.WindingOneTrack p ambient) (origin : WindingOneState p ambient)
    (question : Question origin) :
    (request track origin question).replayExact ((request track origin question).run (answer track origin)).trace =
      .ok (.ok ⟨track.refine question.current.val question.epsilon question.positive, rfl⟩) :=
  ((request track origin question).replayExact_run _).trans (congrArg Except.ok (request_value track origin question))

/-- Changing replies outside this consumed refinement request preserves its complete retained execution. -/
theorem payload_erasure {Payload : Type} (track : Basic.WindingOneTrack p ambient)
    (origin : WindingOneState p ambient) (question : Question origin) (payload : Payload)
    (outside : Payload → Question origin → Reply track origin) :
    (request track origin question).run
        (Boundary.Trace.overlay ((request track origin question).run (answer track origin)).trace (outside payload)) =
      (request track origin question).run (answer track origin) :=
  Protocol.annotation_erasure (request track origin question) (answer track origin) payload outside

/-- The complete strict and accurate refinement produced by a retained winding track. -/
@[expose] def refinement (track : Basic.WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) : Refinement current.raw epsilon :=
  ⟨track.refine current epsilon positive, track.strict current epsilon positive,
    track.accurate current epsilon positive⟩

set_option genInjectivity false in
/-- One actual complete refinement retained at its exact original state and positive request.

The result equation identifies the whole strict and accurate certificate.
The full current state retains all four endpoints and all five clearance
bounds, not only a box identifier or a copied request label.
-/
structure CachedRefinement (track : Basic.WindingOneTrack p ambient) where
  /-- The complete original current state supplied to this refinement. -/ current : WindingOneState p ambient
  /-- The original rational accuracy request. -/ epsilon : Fraction.Rational
  /-- The original request is strictly positive. -/ positive : 0 < epsilon
  /-- The actual complete result returned by checked execution. -/ result : Refinement current.raw epsilon
  /-- The retained result is the original track's whole refinement certificate. -/
  result_eq : result = refinement track current epsilon positive

constructive_injectivity CachedRefinement

/-- Read an exact retained whole refinement or use the same original total track on a miss.

Both complete current-state equality and rational request equality are checked.
A hit transports the retained result only; it runs no refinement producer.
-/
@[expose] def readRefinement (track : Basic.WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    List (CachedRefinement track) → Refinement current.raw epsilon
  | [] => refinement track current epsilon positive
  | entry :: remaining =>
      if sameCurrent : entry.current = current then
        if sameEpsilon : entry.epsilon = epsilon then
          by cases sameCurrent; cases sameEpsilon; exact entry.result
        else readRefinement track current epsilon positive remaining
      else readRefinement track current epsilon positive remaining

/-- Every retained refinement read equals the same original total policy's complete certificate. -/
theorem readRefinement_eq (track : Basic.WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (entries : List (CachedRefinement track)) :
    readRefinement track current epsilon positive entries = refinement track current epsilon positive := by
  induction entries with
  | nil => rfl
  | cons entry remaining ih =>
      unfold readRefinement
      split
      · rename_i sameCurrent
        cases sameCurrent
        split
        · rename_i sameEpsilon
          cases sameEpsilon
          exact entry.result_eq
        · exact ih
      · exact ih

/-- The first exact current-state and request hit returns that same retained whole result. -/
theorem readRefinement_head (track : Basic.WindingOneTrack p ambient)
    (entry : CachedRefinement track) (remaining : List (CachedRefinement track)) :
    readRefinement track entry.current entry.epsilon entry.positive (entry :: remaining) = entry.result := by
  unfold readRefinement
  rewrite [dif_pos rfl, dif_pos rfl]
  rfl

/-- Install a finite checked refinement cache in the original total track.

The same initial state and all positive requests remain supported. Stored
whole results are reused at exact hits; misses keep the original procedure.
This changes execution reuse, not the track's pointwise refinement policy.
-/
@[expose] def withRefinements (track : Basic.WindingOneTrack p ambient)
    (entries : List (CachedRefinement track)) : Basic.WindingOneTrack p ambient where
  initial := track.initial
  refine current epsilon positive := (readRefinement track current epsilon positive entries).state
  nested current epsilon positive := Box.Refinement.StrictInterior.refines
    (readRefinement track current epsilon positive entries).strict
  strict current epsilon positive := (readRefinement track current epsilon positive entries).strict
  accurate current epsilon positive := (readRefinement track current epsilon positive entries).accurate

/-- A checked refinement cache retains the complete original initial state. -/
theorem withRefinements_initial (track : Basic.WindingOneTrack p ambient)
    (entries : List (CachedRefinement track)) : (withRefinements track entries).initial = track.initial := rfl

/-- Cached execution has the same all-input refinement state as the original total policy. -/
theorem withRefinements_refine (track : Basic.WindingOneTrack p ambient)
    (entries : List (CachedRefinement track)) (current : WindingOneState p ambient)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (withRefinements track entries).refine current epsilon positive = track.refine current epsilon positive :=
  congrArg (fun result : Refinement current.raw epsilon => result.state)
    (readRefinement_eq track current epsilon positive entries)

end Observation

end Purelib.RootIsolation.Track
