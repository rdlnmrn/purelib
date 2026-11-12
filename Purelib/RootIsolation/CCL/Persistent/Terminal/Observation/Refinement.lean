module

public import Purelib.RootIsolation.CCL.Persistent.Terminal.Observation
public import Purelib.RootIsolation.Track.Observation
public import Purelib.Computation.Query.Program
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform

/-!
# Terminal point resolution with recorded winding refinement

The polynomial value and the conditional track refinement are separate
requests. The nonroot branch consumes the returned winding state through
the original point-resolution constructor. Replay performs neither callback
and preserves the original raw word, box and exclusion certificates.
-/

public section

namespace Purelib.RootIsolation.CCL.Persistent.Terminal.Observation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Evaluation (Reading)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)
open Purelib.Computation.Query

namespace Refinement

variable {p : CoefficientPolynomial} {ambient : Box}

set_option genInjectivity false in
/-- A polynomial evaluation or an actual original track-refinement request at the retained current state. -/
inductive Question (current : State p ambient) where
  /-- Evaluate this exact terminal candidate. -/ | evaluate (point : Canonical)
  /-- Refine the exact retained numerical state at the supplied positive radius. -/ | refine
      (question : Track.Observation.Question current.numerical)
  deriving @[expose] DecidableEq

set_option genInjectivity false in
/-- The exact polynomial reading or actual cached winding-refinement receipt from the same original track. -/
inductive Reply (track : WindingOneTrack p ambient) (current : State p ambient) where
  /-- Retain the original polynomial and point identity with its cached value. -/ | reading (cached : Reading p)
  /-- Retain the original track's actual state and complete refinement request. -/ | refined
      (cached : Track.Observation.Reply track current.numerical)

set_option genInjectivity false in
/-- An actual terminal reply violates its requested operation, candidate point or positive refinement request. -/
inductive Invalidity (current : State p ambient) where
  /-- Evaluation received a track state instead of a polynomial reading. -/ | expectedReading
  /-- Refinement received a polynomial reading instead of a track state. -/ | expectedRefinement
  /-- The polynomial reading belongs to a different actual point. -/ | point (mismatch : Reading.Mismatch)
  /-- The track receipt belongs to a different actual refinement request. -/ | request
      (mismatch : Track.Observation.Mismatch current.numerical)

/-- The actual cached point-resolution outcome with identity to its same original track/current/point operation. -/
abbrev Realization (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (point : Canonical) :=
  {resolved : Point.PointResolution current point // resolved = Point.resolvePoint degreePositive track current point}

/-- A retained successful resolution is exactly the same original outcome with its defining identity. -/
private theorem realization_eq {degreePositive : 0 < p.natDegree} {track : WindingOneTrack p ambient}
    {current : State p ambient} {point : Canonical} (actual : Realization degreePositive track current point) :
    actual = ⟨Point.resolvePoint degreePositive track current point, rfl⟩ := by
  cases actual with
  | mk resolved resolvedEq =>
      cases resolvedEq
      rfl

/-- Execute the displayed original evaluator or track callback and retain its exact reply. -/
def answer (track : WindingOneTrack p ambient) (current : State p ambient) : Question current → Reply track current
  | .evaluate point => .reading (Reading.ofPoint p point)
  | .refine question => .refined (Track.Observation.answer track current.numerical question)

/-- An evaluation request retains the original polynomial reading at its same actual point. -/
private theorem answer_evaluate_spec (track : WindingOneTrack p ambient) (current : State p ambient)
    (point : Canonical) : answer track current (.evaluate point) = .reading (Reading.ofPoint p point) := rfl

/-- The displayed polynomial callback returns its exact original point/value certificate. -/
theorem answer_evaluate (track : WindingOneTrack p ambient) (current : State p ambient)
    (point : Canonical) : answer track current (.evaluate point) = .reading (Reading.ofPoint p point) :=
  answer_evaluate_spec track current point

/-- A refinement request retains the actual original callback state and same request. -/
private theorem answer_refine_spec (track : WindingOneTrack p ambient) (current : State p ambient)
    (question : Track.Observation.Question current.numerical) :
    answer track current (.refine question) =
      .refined ⟨question, track.refine question.current.val question.epsilon question.positive, rfl⟩ := by
  unfold answer
  dsimp only
  rewrite [Track.Observation.answer_eq]
  rfl

/-- The displayed winding callback returns its same retained request and original state. -/
theorem answer_refine (track : WindingOneTrack p ambient) (current : State p ambient)
    (question : Track.Observation.Question current.numerical) :
    answer track current (.refine question) =
      .refined ⟨question, track.refine question.current.val question.epsilon question.positive, rfl⟩ :=
  answer_refine_spec track current question

/-- Compute the original nonroot exclusion radius directly from the same retained polynomial value. -/
private def refinementQuestion (current : State p ambient) (reading : Reading p) (nonzero : reading.value ≠ 0) :
    Track.Observation.Question current.numerical :=
  Track.Observation.Question.ofCurrent current.numerical
    (Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform.uniformExclusionRadius p ambient
      (Data.Gaussian.Norm.Basic.normSq reading.value))
    (Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform.uniformExclusionRadius_pos p ambient
      (Data.Gaussian.Norm.Basic.normSq_pos nonzero))

/-- Resolve the same retained reading, requesting and consuming the original track state only on its nonroot branch. -/
private def continueReading (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (reading : Reading p) :
    Program (Question current) (Reply track current)
      (Except (Invalidity current) (Realization degreePositive track current reading.point)) :=
  if root : reading.value = 0 then
    if inside : current.numerical.box.Contains reading.point then
      let resolved : Point.PointResolution current reading.point :=
        .exact ⟨reading.point, reading.valueEq.trans root, inside⟩
      have resolvedEq : resolved = Point.resolvePoint degreePositive track current reading.point := by
        unfold Point.resolvePoint
        rewrite [dif_pos (reading.valueEq.trans root), dif_pos inside]
        rfl
      .pure (.ok ⟨resolved, resolvedEq⟩)
    else
      let resolved : Point.PointResolution current reading.point :=
        .excluded current (Box.refines_refl _) rfl inside
      have resolvedEq : resolved = Point.resolvePoint degreePositive track current reading.point := by
        unfold Point.resolvePoint
        rewrite [dif_pos (reading.valueEq.trans root), dif_neg inside]
        rfl
      .pure (.ok ⟨resolved, resolvedEq⟩)
  else
    let question := refinementQuestion current reading root
    (Program.query (.refine question)).map fun reply =>
      match reply with
      | .reading _ => .error .expectedRefinement
      | .refined receipt =>
          match Track.Observation.receive track current.numerical question receipt with
          | .error mismatch => .error (.request mismatch)
          | .ok retained =>
              let nonroot : p.eval reading.point ≠ 0 := fun zero => root (reading.valueEq.symm.trans zero)
              have originalEq : retained.val =
                  Track.Exclusion.Point.refinePastPoint track current.numerical reading.point nonroot :=
                retained.property.trans (Track.Exclusion.Point.refinePastValue_eq
                  track current.numerical reading.point reading.value reading.valueEq root)
              .ok ⟨Point.ofRefinement degreePositive track current reading.point nonroot retained.val originalEq,
                Point.ofRefinement_eq_resolvePoint degreePositive track current reading.point nonroot
                  retained.val originalEq⟩

/-- Retain the original terminal point operation as an expandable evaluator/refinement query construction. -/
def program (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (point : Canonical) :
    Program (Question current) (Reply track current)
      (Except (Invalidity current) (Realization degreePositive track current point)) :=
  (Program.query (.evaluate point)).bind fun reply =>
    match reply with
    | .refined _ => .pure (.error .expectedReading)
    | .reading reading =>
        if same : reading.point = point then
          (continueReading degreePositive track current reading).map fun result =>
            result.map fun resolved => same ▸ resolved
        else .pure (.error (.point ⟨point, reading.point, same⟩))

/-- Resolve one original terminal point with its polynomial and conditional track callbacks fully displayed. -/
def resolvePoint (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (point : Canonical) :
    Protocol (Question current) (Reply track current)
      (Except (Invalidity current) (Realization degreePositive track current point)) :=
  (program degreePositive track current point).protocol

/-- Transport the entire retained point construction to an equal original current state without rebuilding callbacks. -/
@[expose] def castCurrent {degreePositive : 0 < p.natDegree} {track : WindingOneTrack p ambient}
    {first second : State p ambient} {point : Canonical} (same : first = second)
    (construction : Program (Question first) (Reply track first)
      (Except (Invalidity first) (Realization degreePositive track first point))) :
    Program (Question second) (Reply track second)
      (Except (Invalidity second) (Realization degreePositive track second point)) := by
  cases same
  exact construction

/-- Original replies give the same certified point resolution on both root and nonroot branches. -/
private theorem continueReading_value (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (reading : Reading p) :
    ((continueReading degreePositive track current reading).protocol.run (answer track current)).value =
      .ok ⟨Point.resolvePoint degreePositive track current reading.point, rfl⟩ := by
  cases reading with
  | mk point value valueEq =>
      cases valueEq
      unfold continueReading
      by_cases root : p.eval point = 0
      · rewrite [dif_pos root]
        by_cases inside : current.numerical.box.Contains point
        · rewrite [dif_pos inside]
          exact congrArg Except.ok (realization_eq _)
        · rewrite [dif_neg inside]
          exact congrArg Except.ok (realization_eq _)
      · rewrite [dif_neg root, Program.map_execution, Protocol.map_run_value]
        dsimp only [Program.query, Program.protocol,
          Protocol.query, Protocol.bind, Protocol.pure, answer]
        rewrite [Track.Observation.receive_answer]
        exact congrArg Except.ok (realization_eq _)

/-- The fully displayed point operation preserves the exact original point-resolution result for every track. -/
theorem resolvePoint_value (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (point : Canonical) :
    ((resolvePoint degreePositive track current point).run (answer track current)).value =
      .ok ⟨Point.resolvePoint degreePositive track current point, rfl⟩ := by
  unfold resolvePoint
  rewrite [program, Program.bind_execution, Protocol.bind_run_value]
  change ((if same : (Reading.ofPoint p point).point = point then
    ((continueReading degreePositive track current (Reading.ofPoint p point)).map
      (fun result => result.map (fun resolved => same ▸ resolved)))
    else Program.pure (.error (Invalidity.point
      ⟨point, (Reading.ofPoint p point).point, same⟩))).protocol.run
      (answer track current)).value = _
  rewrite [dif_pos (show (Reading.ofPoint p point).point = point from rfl),
    Program.map_execution, Protocol.map_run_value]
  rewrite [continueReading_value]
  rfl

/-- The retained point construction has the same exact original outcome under the original callback replies. -/
private theorem program_value_spec (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (point : Canonical) :
    ((program degreePositive track current point).protocol.run (answer track current)).value =
      .ok ⟨Point.resolvePoint degreePositive track current point, rfl⟩ :=
  resolvePoint_value degreePositive track current point

/-- The expandable point construction retains the exact original resolution and its defining identity. -/
theorem program_value (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (point : Canonical) :
    ((program degreePositive track current point).protocol.run (answer track current)).value =
      .ok ⟨Point.resolvePoint degreePositive track current point, rfl⟩ :=
  program_value_spec degreePositive track current point

/-- The complete source execution retains its original certified point result and actual conditional callback log. -/
theorem resolvePoint_execution (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (point : Canonical) :
    (resolvePoint degreePositive track current point).run (answer track current) =
      ⟨.ok ⟨Point.resolvePoint degreePositive track current point, rfl⟩,
        ((resolvePoint degreePositive track current point).run (answer track current)).trace⟩ :=
  Basic.Execution.ext (resolvePoint_value degreePositive track current point) rfl

/-- Replay reconstructs the original point resolution from its cached polynomial value and winding state. -/
theorem resolvePoint_replay (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (point : Canonical) :
    (resolvePoint degreePositive track current point).replayExact
      ((resolvePoint degreePositive track current point).run (answer track current)).trace =
      .ok (.ok ⟨Point.resolvePoint degreePositive track current point, rfl⟩) :=
  ((resolvePoint degreePositive track current point).replayExact_run _).trans
    (congrArg Except.ok (resolvePoint_value degreePositive track current point))

/-- Outside-query changes preserve the complete point resolution and its conditional evaluation/refinement trace. -/
theorem payload_erasure {Payload : Type} (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (point : Canonical) (payload : Payload)
    (outside : Payload → Question current → Reply track current) :
    let computation := resolvePoint degreePositive track current point
    computation.run (Boundary.Trace.overlay (computation.run (answer track current)).trace (outside payload)) =
      computation.run (answer track current) :=
  Protocol.annotation_erasure (resolvePoint degreePositive track current point) (answer track current) payload outside

end Refinement

end Purelib.RootIsolation.CCL.Persistent.Terminal.Observation
