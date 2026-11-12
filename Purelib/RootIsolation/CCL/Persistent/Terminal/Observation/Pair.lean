module

public import Purelib.RootIsolation.CCL.Persistent.Terminal.Observation.Refinement
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.CCL.Encoding.Parser

/-!
# Both terminal candidates through retained evaluator and track receipts

The second point construction captures the first returned state. Its
identity certificate transports the construction to the original next
state's type without recomputing that state. Both stages share one ordered
query trace and replay uses their same cached polynomial and winding data.
-/

public section

namespace Purelib.RootIsolation.CCL.Persistent.Terminal.Observation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)
open Purelib.Computation.Query

namespace Pair

variable {p : CoefficientPolynomial} {ambient : Box}

/-- The original second-candidate state, used as the nominal index for its retained request and reply types. -/
def secondCurrent (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left : Canonical) : State p ambient :=
  (Point.resolvePoint degreePositive track current left).nextState current

set_option genInjectivity false in
/-- A candidate's evaluation/refinement request, retaining its correct original current-state index. -/
inductive Question (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left : Canonical) where
  /-- The first candidate's request at the original current state. -/ | first (question : Refinement.Question current)
  /-- The second candidate's request at the first resolution's retained next state. -/ | second
      (question : Refinement.Question (secondCurrent degreePositive track current left))

/-- Compare the stage tags and their original current-indexed requests without comparing callback functions. -/
instance {degreePositive : 0 < p.natDegree} {track : WindingOneTrack p ambient}
    {current : State p ambient} {left : Canonical} : DecidableEq (Question degreePositive track current left) :=
  fun first second =>
    match first, second with
    | .first question, .first other =>
        if same : question = other then .isTrue (congrArg Question.first same)
        else .isFalse (fun equal => by cases equal; exact same rfl)
    | .second question, .second other =>
        if same : question = other then .isTrue (congrArg Question.second same)
        else .isFalse (fun equal => by cases equal; exact same rfl)
    | .first _, .second _ => .isFalse (fun equal => by cases equal)
    | .second _, .first _ => .isFalse (fun equal => by cases equal)

set_option genInjectivity false in
/-- An actual candidate receipt with its original point and numerical-state ownership. -/
inductive Reply (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left : Canonical) where
  /-- Retain the first candidate's actual evaluator/refinement reply. -/ | first
      (reply : Refinement.Reply track current)
  /-- Retain the second candidate's actual reply at the same original next state. -/ | second
      (reply : Refinement.Reply track (secondCurrent degreePositive track current left))

set_option genInjectivity false in
/-- A wrong-stage reply or the original point handler's typed invalidity. -/
inductive Invalidity (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left : Canonical) where
  /-- The first stage received a second-stage reply. -/ | expectedFirst
  /-- The second stage received a first-stage reply. -/ | expectedSecond
  /-- Retain the first point handler's actual invalidity. -/ | first (invalid : Refinement.Invalidity current)
  /-- Retain the second point handler's actual invalidity at its same nominal next state. -/ | second
      (invalid : Refinement.Invalidity (secondCurrent degreePositive track current left))

/-- Execute the actual callback from the request without reading a computed canonical next state. -/
def answer (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left : Canonical) :
    Question degreePositive track current left → Reply degreePositive track current left
  | .first question => .first (Refinement.answer track current question)
  | .second (.evaluate point) => .second (.reading (Polynomial.Dense.Gaussian.Evaluation.Reading.ofPoint p point))
  | .second (.refine question) =>
      let state := track.refine question.current.val question.epsilon question.positive
      .second (.refined ⟨question, state, rfl⟩)

/-- Forward a first-candidate request to the shared trace and reject an actual wrong-stage reply. -/
private def firstHandler (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left : Canonical) (question : Refinement.Question current) :
    Protocol (Question degreePositive track current left) (Reply degreePositive track current left)
      (Except (Invalidity degreePositive track current left) (Refinement.Reply track current)) :=
  (Protocol.query (.first question)).map fun reply =>
    match reply with
    | .first cached => .ok cached
    | .second _ => .error .expectedFirst

/-- Forward a second-candidate request while retaining the same next-state owner and rejecting a wrong-stage reply. -/
private def secondHandler (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left : Canonical)
    (question : Refinement.Question (secondCurrent degreePositive track current left)) :
    Protocol (Question degreePositive track current left) (Reply degreePositive track current left)
      (Except (Invalidity degreePositive track current left)
        (Refinement.Reply track (secondCurrent degreePositive track current left))) :=
  (Protocol.query (.second question)).map fun reply =>
    match reply with
    | .first _ => .error .expectedSecond
    | .second cached => .ok cached

/-- Lift the returned point outcome while preserving checked-expansion and point invalidity separately. -/
private def firstResult (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left : Canonical) :
    Protocol (Question degreePositive track current left) (Reply degreePositive track current left)
      (Except (Invalidity degreePositive track current left)
        (Refinement.Realization degreePositive track current left)) :=
  ((Refinement.program degreePositive track current left).expandChecked
    (firstHandler degreePositive track current left)).map fun result =>
      match result with
      | .error invalid => .error invalid
      | .ok executed => executed.value.mapError Invalidity.first

/-- Continue the actual second point construction after transporting only its original current-state index. -/
private def secondResult (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left right : Canonical) (next : State p ambient)
    (nextEq : next = secondCurrent degreePositive track current left) :
    Protocol (Question degreePositive track current left) (Reply degreePositive track current left)
      (Except (Invalidity degreePositive track current left)
        (Refinement.Realization degreePositive track next right)) :=
  let actual := Refinement.program degreePositive track next right
  let retained := Refinement.castCurrent nextEq actual
  (retained.expandChecked (secondHandler degreePositive track current left)).map fun result =>
    match result with
    | .error invalid => .error invalid
    | .ok executed =>
        match executed.value with
        | .error invalid => .error (.second invalid)
        | .ok actual => .ok (nextEq.symm ▸ actual)

/-- The original first-stage replies retain its exact complete point outcome. -/
private theorem firstResult_value (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left : Canonical) :
    ((firstResult degreePositive track current left).run (answer degreePositive track current left)).value =
      .ok ⟨Point.resolvePoint degreePositive track current left, rfl⟩ := by
  rewrite [firstResult, Protocol.map_run_value,
    Program.expandChecked_value _ _ _ (Refinement.answer track current) (fun _ => rfl)]
  dsimp only
  rewrite [Refinement.program_value]
  rfl

/-- The actual second construction retains the original second point outcome after its certified state transport. -/
private theorem secondResult_value (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left right : Canonical) (next : State p ambient)
    (nextEq : next = secondCurrent degreePositive track current left) :
    ((secondResult degreePositive track current left right next nextEq).run
      (answer degreePositive track current left)).value =
      .ok ⟨Point.resolvePoint degreePositive track next right, rfl⟩ := by
  cases nextEq
  rewrite [secondResult]
  dsimp only [Refinement.castCurrent]
  rewrite [Protocol.map_run_value,
    Program.expandChecked_value _ _ _
      (Refinement.answer track (secondCurrent degreePositive track current left)) (fun question => by
        cases question with
        | evaluate point =>
            rewrite [Refinement.answer_evaluate]
            rfl
        | refine question =>
            rewrite [Refinement.answer_refine]
            rfl)]
  dsimp only
  rewrite [Refinement.program_value]
  rfl

/-- Continue the same cached first resolution, retaining the actual next state and both original exclusion proofs. -/
private def continuePair (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left right : Canonical)
    (result : Except (Invalidity degreePositive track current left)
      (Refinement.Realization degreePositive track current left)) :
    Protocol (Question degreePositive track current left) (Reply degreePositive track current left)
      (Except (Invalidity degreePositive track current left) (Finite.PairResolution current left right)) :=
  match result with
  | .error invalid => Protocol.pure (.error invalid)
  | .ok retained =>
      match resolved : retained.val with
      | .exact root => Protocol.pure (.ok (.exact root))
      | .excluded next nested wordEq outside =>
          have nextEq : next = secondCurrent degreePositive track current left :=
            (congrArg (Point.PointResolution.nextState current) resolved).symm.trans
              (congrArg (Point.PointResolution.nextState current) retained.property)
          (secondResult degreePositive track current left right next nextEq).map fun result =>
            match result with
            | .error invalid => .error invalid
            | .ok second =>
                match second.val with
                | .exact root => .ok (.exact ⟨root.point, root.root, nested.contains root.inside⟩)
                | .excluded final finalNested finalWord rightOutside =>
                    .ok (.excluded final (finalNested.trans nested) (finalWord.trans wordEq)
                      (fun inside => outside (finalNested.contains inside)) rightOutside)

/-- Resolve both terminal points with the actual retained first-to-second state and one shared callback trace. -/
def resolvePair (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left right : Canonical) :
    Protocol (Question degreePositive track current left) (Reply degreePositive track current left)
      (Except (Invalidity degreePositive track current left) (Finite.PairResolution current left right)) :=
  (firstResult degreePositive track current left).bind (continuePair degreePositive track current left right)

/-- The same certified first outcome and original second receipts retain the original complete joint resolution. -/
private theorem continuePair_value (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left right : Canonical)
    (retained : Refinement.Realization degreePositive track current left) :
    ((continuePair degreePositive track current left right (.ok retained)).run
      (answer degreePositive track current left)).value =
      .ok (Finite.resolvePair degreePositive track current left right) := by
  cases retained with
  | mk resolved resolvedEq =>
      cases resolved with
      | exact root =>
          unfold continuePair
          dsimp only
          unfold Finite.resolvePair
          rewrite [← resolvedEq]
          rfl
      | excluded next nested wordEq outside =>
          unfold continuePair
          dsimp only
          rewrite [Protocol.map_run_value, secondResult_value]
          dsimp only
          unfold Finite.resolvePair
          rewrite [← resolvedEq]
          dsimp only
          cases Point.resolvePoint degreePositive track next right with
          | exact root => rfl
          | excluded final finalNested finalWord rightOutside => rfl

/-- The combined original receipts return exactly the original two-candidate resolution for every retained track. -/
theorem resolvePair_value (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left right : Canonical) :
    ((resolvePair degreePositive track current left right).run (answer degreePositive track current left)).value =
      .ok (Finite.resolvePair degreePositive track current left right) := by
  rewrite [resolvePair, Protocol.bind_run_value, firstResult_value]
  exact continuePair_value degreePositive track current left right _

/-- Replay reconstructs both original candidate resolutions from their exact retained evaluator/refinement replies. -/
theorem resolvePair_replay (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left right : Canonical) :
    (resolvePair degreePositive track current left right).replayExact
      ((resolvePair degreePositive track current left right).run (answer degreePositive track current left)).trace =
      .ok (.ok (Finite.resolvePair degreePositive track current left right)) :=
  ((resolvePair degreePositive track current left right).replayExact_run _).trans
    (congrArg Except.ok (resolvePair_value degreePositive track current left right))

/-- Read the first original terminal candidate from a retained parser phase, using zero when that phase has none. -/
def leftCandidate (current : State p ambient) : Syntax.Phase → Canonical
  | .sector kind exponent (.two first second) => Terminal.candidateInput
      (State.parse current.word) kind exponent first second false
  | _ => 0

/-- Prepare the retained phase with every actual evaluator and track-refinement callback displayed. -/
def preparePhase (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (selected : Syntax.Phase)
    (phase : (State.parse current.word).phase = selected) :
    Protocol (Question degreePositive track current (leftCandidate current selected))
      (Reply degreePositive track current (leftCandidate current selected))
      (Except (Invalidity degreePositive track current (leftCandidate current selected))
        (Prepare.Preparation current)) :=
  match selected with
  | .sector kind exponent (.two first second) =>
      let left := Terminal.candidateInput
        (State.parse current.word) kind exponent first second false
      let right := Terminal.candidateInput
        (State.parse current.word) kind exponent first second true
      (resolvePair degreePositive track current left right).map fun result =>
        result.map (Prepare.ofResolution current kind exponent first second phase)
  | other => Protocol.pure (.ok (Prepare.preparePhase degreePositive track current other phase))

/-- The complete retained phase preparation has exactly the original certified result for every parser phase. -/
private theorem preparePhase_value_spec (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (selected : Syntax.Phase)
    (phase : (State.parse current.word).phase = selected) :
    ((preparePhase degreePositive track current selected phase).run
      (answer degreePositive track current (leftCandidate current selected))).value =
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
          rewrite [preparePhase, Protocol.map_run_value]
          dsimp only [leftCandidate]
          rewrite [resolvePair_value]
          rfl

/-- Every retained parser phase has the original preparation outcome under the complete recorded callback boundary. -/
theorem preparePhase_value (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (selected : Syntax.Phase)
    (phase : (State.parse current.word).phase = selected) :
    ((preparePhase degreePositive track current selected phase).run
      (answer degreePositive track current (leftCandidate current selected))).value =
      .ok (Prepare.preparePhase degreePositive track current selected phase) :=
  preparePhase_value_spec degreePositive track current selected phase

/-- Compile the actual original parser phase to the full cached polynomial/refinement preparation protocol. -/
def prepare (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) :=
  preparePhase degreePositive track current (State.parse current.word).phase rfl

/-- Complete original preparation returns its same original certified result with every actual callback recorded. -/
private theorem prepare_value_spec (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) :
    ((prepare degreePositive track current).run (answer degreePositive track current
      (leftCandidate current (State.parse current.word).phase))).value =
      .ok (Prepare.prepare degreePositive track current) :=
  preparePhase_value degreePositive track current _ rfl

/-- The cached complete preparation retains the original result for every original track and persistent word. -/
theorem prepare_value (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) :
    ((prepare degreePositive track current).run (answer degreePositive track current
      (leftCandidate current (State.parse current.word).phase))).value =
      .ok (Prepare.prepare degreePositive track current) :=
  prepare_value_spec degreePositive track current

/-- Complete preparation retains its original outcome and the ordered callbacks actually reached by its parser phase. -/
theorem prepare_execution (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) :
    let computation := prepare degreePositive track current
    let oracle := answer degreePositive track current
      (leftCandidate current (State.parse current.word).phase)
    computation.run oracle =
      ⟨.ok (Prepare.prepare degreePositive track current), (computation.run oracle).trace⟩ :=
  Basic.Execution.ext (prepare_value degreePositive track current) rfl

/-- Replay rebuilds the same preparation using only its cached polynomial and winding-state replies. -/
theorem prepare_replay (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) :
    let computation := prepare degreePositive track current
    let oracle := answer degreePositive track current
      (leftCandidate current (State.parse current.word).phase)
    computation.replayExact (computation.run oracle).trace = .ok (.ok (Prepare.prepare degreePositive track current)) :=
  ((prepare degreePositive track current).replayExact_run _).trans
    (congrArg Except.ok (prepare_value degreePositive track current))

/-- Outside-stage-query changes preserve the entire joint resolution and its ordered conditional callback trace. -/
theorem payload_erasure {Payload : Type} (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (left right : Canonical) (payload : Payload)
    (outside : Payload → Question degreePositive track current left → Reply degreePositive track current left) :
    let computation := resolvePair degreePositive track current left right
    let oracle := answer degreePositive track current left
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (resolvePair degreePositive track current left right)
    (answer degreePositive track current left) payload outside

/-- Changes outside the reached preparation requests preserve its whole certified outcome and callback trace. -/
theorem prepare_payload_erasure {Payload : Type}
    (degreePositive : 0 < p.natDegree) (track : WindingOneTrack p ambient)
    (current : State p ambient) (payload : Payload)
    (outside : Payload →
      Question degreePositive track current
        (leftCandidate current (State.parse current.word).phase) →
      Reply degreePositive track current
        (leftCandidate current (State.parse current.word).phase)) :
    let computation := prepare degreePositive track current
    let oracle := answer degreePositive track current
      (leftCandidate current (State.parse current.word).phase)
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (prepare degreePositive track current)
    (answer degreePositive track current
      (leftCandidate current (State.parse current.word).phase)) payload outside

end Pair

end Purelib.RootIsolation.CCL.Persistent.Terminal.Observation
