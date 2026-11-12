module

public import Purelib.RootIsolation.CCL.Persistent.Terminal.Finite
public import Purelib.RootIsolation.CCL.Persistent.Terminal.Prepare
public import Purelib.Polynomial.Dense.Gaussian.Evaluation.Observation
public import Purelib.Computation.Query.Boundary
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.Track.Exclusion.Point

open Purelib.Data.CCL.Encoding.Parser

/-!
# Polynomial checks below persistent terminal preparation

The displayed query returns the original polynomial's certified cached value.
Root decisions and exclusion radii consume that same value. The retained
track, current state, raw prefix and winding owner remain the original ones.
Wrong-point replies are explicit errors. Exact-root certificates remain
symbolic output and have no numerical rational-replacement claim.
-/

public section

namespace Purelib.RootIsolation.CCL.Persistent.Terminal

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Evaluation (Reading)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)
open Purelib.Computation.Query

namespace Observation

variable {p : CoefficientPolynomial} {ambient : Box}

/-- Resolve a point using its retained exact polynomial reading and the original track.

The nonroot branch computes its exclusion radius from the supplied cache.
The returned certificates retain the same source polynomial and current box.
-/
@[expose] def resolveReading (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) (reading : Reading p) :
    Point.PointResolution current reading.point :=
  if root : reading.value = 0 then
    if inside : current.numerical.box.Contains reading.point then
      .exact ⟨reading.point, reading.valueEq.trans root, inside⟩
    else .excluded current (Box.refines_refl _) rfl inside
  else
    let numerical := Track.Exclusion.Point.refinePastValue track current.numerical
      reading.point reading.value reading.valueEq root
    let nonroot : p.eval reading.point ≠ 0 := fun zero => root (reading.valueEq.symm.trans zero)
    have numericalEq := Track.Exclusion.Point.refinePastValue_eq track current.numerical
      reading.point reading.value reading.valueEq root
    have nested : numerical.box.Refines current.numerical.box := by
      change (Track.Exclusion.Point.refinePastValue track current.numerical
        reading.point reading.value reading.valueEq root).box.Refines current.numerical.box
      rewrite [numericalEq]
      exact Track.Exclusion.Point.refinePastPoint_refines track current.numerical reading.point nonroot
    .excluded (current.refine numerical nested) nested rfl (by
      change ¬(Track.Exclusion.Point.refinePastValue track current.numerical
        reading.point reading.value reading.valueEq root).box.Contains reading.point
      rewrite [numericalEq]
      exact Track.Exclusion.Point.refinePastPoint_excludes
        degreePositive track current.numerical reading.point nonroot)

/-- Resolving a retained exact value gives exactly the original point-resolution output. -/
theorem resolveReading_eq (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) (reading : Reading p) :
    resolveReading degreePositive track current reading =
      Point.resolvePoint degreePositive track current reading.point := by
  cases reading with
  | mk point value valueEq =>
      cases valueEq
      rfl

/-- Compile one original terminal-point resolution with its actual polynomial evaluation displayed. -/
@[expose] def resolvePoint (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) (point : Canonical) :
    Protocol Canonical (Reading p) (Except Reading.Mismatch (Point.PointResolution current point)) :=
  (Reading.request p point).map fun reply =>
    match reply with
    | .error mismatch => .error mismatch
    | .ok retained => .ok (retained.property ▸ resolveReading degreePositive track current retained.val)

/-- The displayed resolution returns exactly the original certified point-resolution result. -/
theorem resolvePoint_value (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) (point : Canonical) :
    ((resolvePoint degreePositive track current point).run (Reading.ofPoint p)).value =
      .ok (Point.resolvePoint degreePositive track current point) := by
  rewrite [resolvePoint, Protocol.map_run_value, Reading.request_value]
  exact congrArg Except.ok (resolveReading_eq degreePositive track current (Reading.ofPoint p point))

/-- The complete point-resolution execution retains the original certified result and its exact evaluator request. -/
theorem resolvePoint_execution (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) (point : Canonical) :
    (resolvePoint degreePositive track current point).run (Reading.ofPoint p) =
      ⟨.ok (Point.resolvePoint degreePositive track current point), [⟨point, Reading.ofPoint p point⟩]⟩ :=
  Basic.Execution.ext (resolvePoint_value degreePositive track current point)
    ((Protocol.map_run_trace _ _ _).trans (Reading.request_trace p point _))

/-- Resolve the two original preparation candidates, retaining the actual first refined state for the second query. -/
@[expose] def resolvePair (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) (left right : Canonical) :
    Protocol Canonical (Reading p) (Except Reading.Mismatch (Finite.PairResolution current left right)) :=
  (resolvePoint degreePositive track current left).bind fun result =>
    match result with
    | .error mismatch => Protocol.pure (.error mismatch)
    | .ok (.exact root) => Protocol.pure (.ok (.exact root))
    | .ok (.excluded next nested wordEq outside) =>
        (resolvePoint degreePositive track next right).map fun result =>
          match result with
          | .error mismatch => .error mismatch
          | .ok (.exact root) => .ok (.exact ⟨root.point, root.root, nested.contains root.inside⟩)
          | .ok (.excluded final finalNested finalWord rightOutside) =>
              .ok (.excluded final (finalNested.trans nested) (finalWord.trans wordEq)
                (fun inside => outside (finalNested.contains inside)) rightOutside)

/-- The enlarged preparation protocol returns exactly the original two-candidate resolution. -/
theorem resolvePair_value (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) (left right : Canonical) :
    ((resolvePair degreePositive track current left right).run (Reading.ofPoint p)).value =
      .ok (Finite.resolvePair degreePositive track current left right) := by
  rewrite [resolvePair, Protocol.bind_run_value, resolvePoint_value, Finite.resolvePair]
  cases first : Point.resolvePoint degreePositive track current left with
  | exact root => rfl
  | excluded next nested wordEq outside =>
      dsimp only
      rewrite [Protocol.map_run_value, resolvePoint_value]
      cases second : Point.resolvePoint degreePositive track next right with
      | exact root => rfl
      | excluded final finalNested finalWord rightOutside => rfl

/-- Compile a retained parser phase, exposing its polynomial checks only in the actual terminal phase. -/
@[expose] def preparePhase (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (selected : Syntax.Phase)
    (phase : (State.parse current.word).phase = selected) :
    Protocol Canonical (Reading p) (Except Reading.Mismatch (Prepare.Preparation current)) :=
  match selected with
  | .sector kind exponent (.two first second) =>
      let left := Terminal.candidateInput
        (State.parse current.word) kind exponent first second false
      let right := Terminal.candidateInput
        (State.parse current.word) kind exponent first second true
      (resolvePair degreePositive track current left right).map fun result =>
        result.map (Prepare.ofResolution current kind exponent first second phase)
  | other => Protocol.pure (.ok (Prepare.preparePhase degreePositive track current other phase))

/-- The compiled retained phase returns exactly the original phase preparation. -/
theorem preparePhase_value (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (selected : Syntax.Phase)
    (phase : (State.parse current.word).phase = selected) :
    ((preparePhase degreePositive track current selected phase).run (Reading.ofPoint p)).value =
      .ok (Prepare.preparePhase degreePositive track current selected phase) := by
  cases selected with
  | initial => rfl
  | highUnary count => rfl
  | lowUnary count => rfl
  | loopUnary count => rfl
  | sector kind exponent bits =>
      cases bits with
      | zero => rfl
      | one first => rfl
      | two first second =>
          rewrite [preparePhase, Protocol.map_run_value, resolvePair_value]
          rfl

/-- Compile the original terminal preparation from its same retained raw parser phase. -/
@[expose] def prepare (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    Protocol Canonical (Reading p) (Except Reading.Mismatch (Prepare.Preparation current)) :=
  preparePhase degreePositive track current (State.parse current.word).phase rfl

/-- The enlarged preparation returns exactly the original certified preparation for every parser phase. -/
theorem prepare_value (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    ((prepare degreePositive track current).run (Reading.ofPoint p)).value =
      .ok (Prepare.prepare degreePositive track current) := by
  exact preparePhase_value degreePositive track current _ rfl

/-- Retain the actual polynomial-check trace of the original preparation once. -/
@[expose] def recordPreparation (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    Basic.Execution Canonical (Reading p) (Except Reading.Mismatch (Prepare.Preparation current)) :=
  (prepare degreePositive track current).run (Reading.ofPoint p)

/-- The complete preparation execution has the original dependent result and the same actual check transcript. -/
theorem preparation_execution (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    (prepare degreePositive track current).run (Reading.ofPoint p) =
      ⟨.ok (Prepare.prepare degreePositive track current),
        (recordPreparation degreePositive track current).trace⟩ :=
  Basic.Execution.ext (prepare_value degreePositive track current) rfl

/-- Replay at the retained original track returns its complete certified preparation from the displayed checks. -/
theorem preparation_replay (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    (prepare degreePositive track current).replayExact (recordPreparation degreePositive track current).trace =
      .ok (.ok (Prepare.prepare degreePositive track current)) :=
  ((prepare degreePositive track current).replayExact_run (Reading.ofPoint p)).trans
    (congrArg Except.ok (prepare_value degreePositive track current))

/-- Outside-check payload changes preserve the complete certified preparation and the full ordered evaluator trace. -/
theorem preparation_payload_erasure {Payload : Type} (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (payload : Payload) (outside : Payload → Canonical → Reading p) :
    (prepare degreePositive track current).run
        (Boundary.Trace.overlay (recordPreparation degreePositive track current).trace (outside payload)) =
      recordPreparation degreePositive track current :=
  Protocol.annotation_erasure (prepare degreePositive track current) (Reading.ofPoint p) payload outside

/-- Outside-trace changes preserve the whole two-candidate preparation, including both original dependent owners. -/
theorem payload_erasure {Payload : Type} (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) (left right : Canonical)
    (payload : Payload) (outside : Payload → Canonical → Reading p) :
    let computation := resolvePair degreePositive track current left right
    computation.run (Boundary.Trace.overlay (computation.run (Reading.ofPoint p)).trace (outside payload)) =
      computation.run (Reading.ofPoint p) :=
  Protocol.annotation_erasure (resolvePair degreePositive track current left right) (Reading.ofPoint p) payload outside

end Observation

end Purelib.RootIsolation.CCL.Persistent.Terminal
