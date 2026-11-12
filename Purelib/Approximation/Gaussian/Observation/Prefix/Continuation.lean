module
public import Purelib.Data.CCL.Encoding.Prefix.Completion

public import Purelib.Approximation.Gaussian.Observation.Prefix.Transcript
public import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.History
import Purelib.Computation.Query.Path
import Purelib.Approximation.Gaussian.Observation.Cursor.Request
import Purelib.Data.List.Append
import Purelib.Data.List.Membership

/-!
# Finite canonical rational continuation

The interpreter consumes retained finite affine cursor code and saved
numerical replies. New requests use the original canonical local decision,
with an exact-point ambient ball and explicit affine-terminal payment.
No original proper-box construction or source callback is retained.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Prefix.Continuation

open Purelib
open Purelib.Data.CCL
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Computation
open Purelib.Computation.Query
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

namespace Code

/-- Compute a canonical terminal word from the same valid finite code and its retained exact integral fraction.

The original cursor calculates its bound, actual suffix and projective completion.
The displayed fraction is already cached numerical data; this operation does not
change the old reply or normalize the reading again.
-/
def finishEncoding (code : Code) (valid : code.Valid) (fraction : Purelib.Data.GaussianInt.Fraction)
    (numeratorNonzero : fraction.numerator ≠ 0) (fractionValue : fraction.value = code.point) :
    Encoding.Prefix.Cursor.FinishedEncoding code.cursor fraction numeratorNonzero :=
  code.cursor.finishEncoding valid.cursor fraction numeratorNonzero fractionValue

namespace Valid

/-- Read the same code's original affine-tail candidate without recomputing any parser, inverse chart or tail. -/
def candidate {code : Code} (valid : code.Valid) : Reply.Candidate code.reply code.point := by
  have stateMatrix : code.reply.state.matrix = code.cursor.state.matrix :=
    congrArg Encoding.Parser.State.matrix valid.stateEq
  exact
    { tail := code.cursor.tail
      stateSpec := valid.stateEq.trans
        (valid.cursor.stateSpec.trans (congrArg Encoding.Parser.State.parse valid.wordEq.symm))
      determinant := (congrArg (fun state : Encoding.Parser.State =>
        Matrix2.Matrix2.determinant state.matrix) valid.stateEq).symm ▸
          valid.cursor.determinant
      inverseSpec := valid.inverseEq.trans
        (valid.cursor.inverseSpec.trans
          (congrArg Matrix2.BoundaryAdjugate.adjugate stateMatrix.symm))
      tailSpec := valid.cursor.tailSpec.trans
        (congrArg (fun matrix => Homography.Basic.homographic matrix code.point)
          valid.inverseEq.symm)
      represented := valid.stateEq.symm ▸ valid.cursor.represents
      inside := valid.inside
      stopped := by
        intro flag
        exact valid.stateEq.symm ▸ valid.stopped flag }

end Valid

/-- Display the same exact canonical cursor with a supplied ball and an explicit request-terminal flag. -/
@[expose] def replyOfCursor (cursor : Encoding.Prefix.Cursor) (ball : Enclosure.Ball) (terminal : Bool) : Reply :=
  ⟨cursor.word, cursor.state, cursor.inverseMatrix, ball, terminal⟩

end Code

set_option genInjectivity false in
/-- One finite canonical request preserves its reading and prefix, with full payment or an explicit affine terminal. -/
structure RequestResult (earlier : Code) (request : Cursor.Request) where
  /-- The actual computed or retained next finite code. -/ next : Code
  /-- The next code has its same complete affine and numerical validity. -/ valid : next.Valid
  /-- The same Gaussian-rational reading is retained. -/ pointEq : next.point = earlier.point
  /-- The exact previously exposed raw word persists. -/ wordPrefix : earlier.reply.word.IsPrefix next.reply.word
  /-- An additional-bit request returns at most its actual supplied count. -/ lengthBound :
    ∀ count, request = .bits count → next.reply.word.length ≤ earlier.reply.word.length + count
  /-- A bit request pays its count unless that same returned affine prefix has no admissible next bit. -/ completion :
    ∀ count, request = .bits count → next.reply.word.length = earlier.reply.word.length + count ∨
      ∀ bit, ¬Encoding.Parser.Semantics.Prefix.CanStep next.cursor.state next.point bit
  /-- An enclosure request pays its original strict positive squared target. -/ accurate :
    ∀ target positive, request = .enclosure target positive → next.reply.ball.radiusSq < target

namespace Code

/-- Execute a later canonical request from finite code, preserving its same reading and explicit terminal convention. -/
def request (code : Code) (valid : code.Valid) (request : Cursor.Request) : RequestResult code request := by
  cases request with
  | bits count =>
      let result := code.cursor.request valid.cursor count
      let terminal := if result.suffix.length = count then false else true
      have stopped : terminal = true → ∀ bit,
          ¬Encoding.Parser.Semantics.Prefix.CanStep result.next.state result.next.point bit := by
        intro flag
        unfold terminal at flag
        split at flag
        · nomatch flag
        · rename_i notPaid
          cases result.completion with
          | inl paid => exact (notPaid paid).elim
          | inr stopped => exact stopped
      let reply := replyOfCursor result.next (Enclosure.Ball.point result.next.point) terminal
      let next : Code := ⟨result.next, reply⟩
      have lengthEq : next.reply.word.length = code.reply.word.length + result.suffix.length := by
        change result.next.word.length = _
        rewrite [result.wordEq, Data.List.Append.length_append, ← valid.wordEq]
        rfl
      exact
        { next := next
          valid := ⟨result.valid, rfl, rfl, rfl, Enclosure.Ball.contains_point _, stopped⟩
          pointEq := result.pointEq
          wordPrefix := valid.wordEq.symm ▸ result.wordPrefix
          lengthBound := by
            intro requested same
            cases same
            exact lengthEq ▸ Nat.add_le_add_left result.lengthBound _
          completion := by
            intro requested same
            cases same
            cases result.completion with
            | inl paid => exact .inl (lengthEq.trans (congrArg (Nat.add code.reply.word.length) paid))
            | inr stopped => exact .inr stopped
          accurate := by intro _ _ impossible; nomatch impossible }
  | enclosure target positive =>
      let reply := replyOfCursor code.cursor (Enclosure.Ball.point code.point) false
      let next : Code := ⟨code.cursor, reply⟩
      exact
        { next := next
          valid := ⟨valid.cursor, rfl, rfl, rfl, Enclosure.Ball.contains_point _,
            fun impossible => by nomatch impossible⟩
          pointEq := rfl
          wordPrefix := ⟨[], (Data.List.Append.append_nil _).trans valid.wordEq⟩
          lengthBound := by intro _ impossible; nomatch impossible
          completion := by intro _ impossible; nomatch impossible
          accurate := by intro requested requestedPositive same; cases same; exact positive }

end Code

/-- Retain the same valid current code and exact unconsumed certified saved suffix. -/
abbrev State := Query.History.State Code.Valid Step.Valid

namespace State

set_option genInjectivity false in
/-- An interpreted request retains its complete payment and the same next code's remaining saved chain. -/
structure Result (earlier : State) (request : Cursor.Request) where
  /-- The actual next finite code and complete prefix or accuracy certificate. -/ result :
    RequestResult earlier.code request
  /-- The exact unconsumed saved suffix on the resulting path. -/ remaining : List Step
  /-- The suffix begins at that same computed or retained next code. -/ chain : Chain result.next remaining

namespace Result

/-- Project the exact next code and remaining saved suffix without repeating any request. -/
@[expose] def state {earlier : State} {request : Cursor.Request} (result : Result earlier request) : State :=
  ⟨result.result.next, result.result.valid, result.remaining, result.chain⟩

end Result

/-- Interpret a request using its matching saved transition or the same current finite rational cursor.

A different request leaves the saved path permanently. Its fallback starts
at the exact current code, so all later requests preserve the actually exposed
prefix and the same rational reading instead of overlaying unrelated replies.
-/
def request (state : State) (request : Cursor.Request) : Result state request := by
  match Query.History.State.select state request with
  | .fresh => exact ⟨state.code.request state.valid request, [], .nil _⟩
  | .saved step remaining saved same =>
      have chain : Chain state.code (step :: remaining) := saved ▸ state.chain
      have head := chain.head
      let result : RequestResult state.code request :=
        { next := step.next
          valid := head.nextValid
          pointEq := head.pointEq
          wordPrefix := head.wordPrefix
          lengthBound := by
            intro count requested
            exact Nat.le_of_eq (head.length count (same.symm.trans requested))
          completion := by
            intro count requested
            exact .inl (head.length count (same.symm.trans requested))
          accurate := by
            intro target positive requested
            exact head.accurate target positive (same.symm.trans requested) }
      exact ⟨result, remaining, chain.tail⟩

/-- Consume one interpreted request's same next code and saved suffix. -/
def step (state : State) (request : Cursor.Request) : State := (state.request request).state

/-- A matching saved request retains the exact cached next code and remaining suffix. -/
private theorem step_saved_specification (code : Code) (valid : code.Valid) (saved : Step) (remaining : List Step)
    (chain : Chain code (saved :: remaining)) :
    step (Query.History.State.mk code valid (saved :: remaining) chain) saved.request =
      Query.History.State.mk saved.next chain.head.nextValid remaining chain.tail := by
  unfold step request Query.History.State.select
  dsimp only
  rewrite [dif_pos rfl]
  rfl

/-- A matching saved request uses its original complete finite code without invoking the fallback controller. -/
theorem step_saved (code : Code) (valid : code.Valid) (saved : Step) (remaining : List Step)
    (chain : Chain code (saved :: remaining)) :
    step (Query.History.State.mk code valid (saved :: remaining) chain) saved.request =
      Query.History.State.mk saved.next chain.head.nextValid remaining chain.tail :=
  step_saved_specification code valid saved remaining chain

/-- Every interpreted request retains the same rational reading on saved and divergent paths. -/
private theorem step_point_specification (state : State) (request : Cursor.Request) :
    (state.step request).code.point = state.code.point := (state.request request).result.pointEq

/-- The interpreted saved or future transition retains its exact fixed rational reading. -/
theorem step_point (state : State) (request : Cursor.Request) :
    (state.step request).code.point = state.code.point := step_point_specification state request

/-- A saved or future canonical request retains the exact previously exposed affine word. -/
private theorem step_prefix_specification (state : State) (request : Cursor.Request) :
    state.code.reply.word.IsPrefix (state.step request).code.reply.word :=
  (state.request request).result.wordPrefix

/-- Every saved or later canonical request preserves the exact actual previously exposed raw prefix. -/
theorem step_prefix (state : State) (request : Cursor.Request) :
    state.code.reply.word.IsPrefix (state.step request).code.reply.word := step_prefix_specification state request

/-- A canonical additional-bit request never exposes more than its actual supplied count. -/
private theorem step_length_specification (state : State) (count : Nat) :
    (state.step (.bits count)).code.reply.word.length ≤ state.code.reply.word.length + count :=
  (state.request (.bits count)).result.lengthBound count rfl

/-- A saved or later canonical bit request returns at most the supplied additional count. -/
theorem step_length_bound (state : State) (count : Nat) :
    (state.step (.bits count)).code.reply.word.length ≤ state.code.reply.word.length + count :=
  step_length_specification state count

/-- The canonical request projection retains its exact paid-count or affine-terminal certificate. -/
private theorem step_completion_specification (state : State) (count : Nat) :
    (state.step (.bits count)).code.reply.word.length = state.code.reply.word.length + count ∨
      ∀ bit, ¬Encoding.Parser.Semantics.Prefix.CanStep
        (state.step (.bits count)).code.cursor.state (state.step (.bits count)).code.point bit :=
  (state.request (.bits count)).result.completion count rfl

/-- Every canonical bit request pays its count or reports no further admissible affine bit at the same reading. -/
theorem step_completion (state : State) (count : Nat) :
    (state.step (.bits count)).code.reply.word.length = state.code.reply.word.length + count ∨
      ∀ bit, ¬Encoding.Parser.Semantics.Prefix.CanStep
        (state.step (.bits count)).code.cursor.state (state.step (.bits count)).code.point bit :=
  step_completion_specification state count

/-- The actual next canonical enclosure uses its same original positive target. -/
private theorem step_accuracy_specification (state : State) (target : Fraction.Rational) (positive : 0 < target) :
    (state.step (.enclosure target positive)).code.reply.ball.radiusSq < target :=
  (state.request (.enclosure target positive)).result.accurate target positive rfl

/-- Every saved or later canonical enclosure request pays its exact strict positive target. -/
theorem step_accurate (state : State) (target : Fraction.Rational) (positive : 0 < target) :
    (state.step (.enclosure target positive)).code.reply.ball.radiusSq < target :=
  step_accuracy_specification state target positive

/-- Execute the same finite path, consuming saved transitions while its requests continue to match. -/
@[expose] def execute : State → List Cursor.Request → State := Query.History.execute step

/-- Appending a request path continues from its actual previously interpreted state. -/
theorem execute_append (state : State) (earlier later : List Cursor.Request) :
    state.execute (earlier ++ later) = (state.execute earlier).execute later :=
  Query.History.execute_append step state earlier later

/-- Executing the exact saved requests consumes the original stored codes and returns their actual final cache. -/
theorem execute_saved (code : Code) (valid : code.Valid) (saved : List Step) (chain : Chain code saved) :
    execute (Query.History.State.mk code valid saved chain) (saved.map (fun step : Step => step.request)) =
      Query.History.State.mk (History.endpointFrom code saved)
        (History.endpointFrom_valid code valid saved chain) [] (.nil _) := by
  induction saved generalizing code with
  | nil => rfl
  | cons saved remaining induction =>
      change execute (step (Query.History.State.mk code valid (saved :: remaining) chain) saved.request)
        (remaining.map (fun step : Step => step.request)) = _
      rewrite [step_saved]
      exact induction saved.next chain.head.nextValid chain.tail

/-- Every finite saved or divergent request path retains the same exact rational reading. -/
theorem execute_point (state : State) (requests : List Cursor.Request) :
    (state.execute requests).code.point = state.code.point :=
  Query.History.execute_reading step (fun state : State => state.code.point) step_point state requests

/-- Answer a full original path question from this same finite rational history state. -/
@[expose] def answer (state : State) (question : Cursor.Question) : Reply := (state.execute question.path).code.reply

/-- Every saved exchange is reproduced exactly after its actual preceding path has been interpreted. -/
theorem answers_from (start : State) (path : List Cursor.Request) (code : Code) (valid : code.Valid)
    (saved : List Step) (chain : Chain code saved)
    (reached : start.execute path = Query.History.State.mk code valid saved chain) :
    Basic.Answers start.answer (History.traceFrom path saved) :=
  Query.History.State.answers_from (validStep := Step.Valid) (fun _ _ head => head.nextValid) step Code.reply
    step_saved start path code valid saved chain reached

end State

namespace History

/-- Interpret valid finite history code at its retained starting reply and exact saved transition chain. -/
@[expose] def state (history : History) (valid : History.Valid history) : State :=
  ⟨history.initial, valid.initial, history.steps, valid.chain⟩

/-- Read the exact last saved code as a certified state with no saved suffix remaining. -/
@[expose] def endpointState (history : History) (valid : history.Valid) : State :=
  ⟨history.endpoint, history.endpoint_valid valid, [], .nil _⟩

/-- The actual saved request list reaches the retained final state by consuming the original caches. -/
theorem execute_endpoint (history : History) (valid : history.Valid) :
    (history.state valid).execute (history.steps.map (fun step : Step => step.request)) = history.endpointState valid :=
  State.execute_saved history.initial valid.initial history.steps valid.chain

/-- Answer mixed numerical path questions using only finite history code and its fixed rational cursor interpreter. -/
@[expose] def interpret (history : History) (valid : History.Valid history) : Cursor.Question → Reply :=
  (history.state valid).answer

/-- Finite history code reproduces every original saved complete numerical reply. -/
theorem answers (history : History) (valid : History.Valid history) :
    Basic.Answers (history.interpret valid) history.trace :=
  State.answers_from (history.state valid) [] history.initial valid.initial history.steps valid.chain rfl

/-- Every interpreted saved or future reply has its same certified affine candidate at the retained history reading. -/
def interpret_candidate (history : History) (valid : history.Valid) (question : Cursor.Question) :
    Reply.Candidate (history.interpret valid question) history.initial.point :=
  ((history.state valid).execute_point question.path) ▸
    ((history.state valid).execute question.path).valid.candidate

/-- Every interpreted canonical reply preserves the word actually exposed at its exact preceding path. -/
theorem interpret_prefix (history : History) (valid : history.Valid) (question : Cursor.Question) :
    ((history.state valid).execute question.previous).code.reply.word.IsPrefix
      (history.interpret valid question).word := by
  change ((history.state valid).execute question.previous).code.reply.word.IsPrefix
    ((history.state valid).execute question.path).code.reply.word
  unfold Cursor.Question.path Path.Question.path
  rewrite [State.execute_append]
  exact ((history.state valid).execute question.previous).step_prefix question.request

/-- Canonical future bit requests never expose more than their actual additional requested count. -/
theorem interpret_length_bound (history : History) (valid : history.Valid)
    (previous : List Cursor.Request) (count : Nat) :
    (history.interpret valid ⟨previous, .bits count⟩).word.length ≤
      ((history.state valid).execute previous).code.reply.word.length + count := by
  change ((history.state valid).execute (previous ++ [.bits count])).code.reply.word.length ≤ _
  rewrite [State.execute_append]
  exact ((history.state valid).execute previous).step_length_bound count

/-- Every positive canonical enclosure request receives its exact strict target on saved and divergent paths. -/
theorem interpret_accurate (history : History) (valid : history.Valid)
    (previous : List Cursor.Request) (target : Fraction.Rational) (positive : 0 < target) :
    (history.interpret valid ⟨previous, .enclosure target positive⟩).ball.radiusSq < target := by
  change ((history.state valid).execute (previous ++ [.enclosure target positive])).code.reply.ball.radiusSq < target
  rewrite [State.execute_append]
  exact ((history.state valid).execute previous).step_accurate target positive

end History

namespace Result

/-- The terminal construction keeps the original admitted endpoint and its cached integral fraction. -/
@[expose] def Terminal {trace : Basic.Trace Cursor.Question Reply} (admitted : Admitted trace) : Type :=
  Encoding.Prefix.Cursor.FinishedEncoding admitted.endpoint.cursor admitted.realization.fraction
    admitted.realization.numeratorNonzero

end Result

set_option genInjectivity false in
/-- Retain an original canonical admission and that same exact finite rational history for numerical continuation. -/
structure Result (trace : Basic.Trace Cursor.Question Reply) where
  /-- The original source-produced canonical admission and its actual proper-box survivor. -/ admitted : Admitted trace
  /-- The same finite rational history used by the source-free interpreter. -/ history : History
  /-- The interpreter consumes the exact original admission's cached history. -/ historyEq : history = admitted.history
  /-- The same retained finite history has its complete canonical validity. -/ valid : history.Valid
  /-- The bound, actual suffix, stopped cursor and canonical word computed once from the original endpoint. -/
  terminal : Result.Terminal admitted

/-- Construct the whole-history continuation and automatic terminal encoding from the same admitted finite data.

The original history and numerical balls are retained exactly. The endpoint's
cached fraction supplies the full encoder once, which computes the remaining
bound, actual stopped affine cursor and compatible projective terminal word.
-/
def ofAdmitted {trace : Basic.Trace Cursor.Question Reply} (admitted : Admitted trace) : Result trace :=
  ⟨admitted, admitted.history, rfl, admitted.historyValid,
    admitted.endpoint.finishEncoding admitted.endpointValid admitted.realization.fraction
      admitted.realization.numeratorNonzero
        (admitted.realization.fractionValue.trans admitted.endpointPoint.symm)⟩

/-- The automatic constructor retains the exact original admitted owner. -/
private theorem ofAdmitted_specification {trace : Basic.Trace Cursor.Question Reply} (admitted : Admitted trace) :
    (ofAdmitted admitted).admitted = admitted := rfl

/-- Automatic continuation retains the exact original admitted history and its rational realization owner. -/
theorem ofAdmitted_admitted {trace : Basic.Trace Cursor.Question Reply} (admitted : Admitted trace) :
    (ofAdmitted admitted).admitted = admitted := ofAdmitted_specification admitted

namespace Result

/-- Read the same original cached endpoint with an exhausted saved suffix, without executing any query. -/
@[expose] def endpointState {trace : Basic.Trace Cursor.Question Reply} (result : Result trace) : State :=
  ⟨result.admitted.endpoint,
    result.admitted.endpointValid,
    [], .nil _⟩

/-- The continuation's exact saved request list reaches its retained endpoint state. -/
theorem execute_endpoint {trace : Basic.Trace Cursor.Question Reply} (result : Result trace) :
    (result.history.state result.valid).execute (result.history.steps.map (fun step : Step => step.request)) =
      result.endpointState := by
  rewrite [History.execute_endpoint]
  have codeEq : result.history.endpoint = result.admitted.endpoint :=
    (congrArg History.endpoint result.historyEq).trans result.admitted.endpointEq.symm
  have emptyEq : ∀ (left right : Code) (leftValid : left.Valid) (rightValid : right.Valid), left = right →
      (Query.History.State.mk left leftValid [] (Query.History.Chain.nil left) : State) =
        Query.History.State.mk right rightValid [] (Query.History.Chain.nil right) := by
    intro left right leftValid rightValid same
    cases same
    rfl
  exact emptyEq _ _ _ _ codeEq

/-- The saved endpoint retains the same original proper-box sample and its cached affine parser realization. -/
theorem endpoint_cursor {trace : Basic.Trace Cursor.Question Reply} (result : Result trace) :
    result.endpointState.code.cursor = (Encoding.Prefix.Cursor.ofRealization result.admitted.realization).val :=
  result.admitted.endpointCursor

/-- The automatically finished word is literally the original full encoder output on the same cached fraction. -/
theorem terminal_word {trace : Basic.Trace Cursor.Question Reply} (result : Result trace) :
    result.terminal.completion.word =
      Encoding.Encoder.Integral.encode result.admitted.realization.fraction
        result.admitted.realization.numeratorNonzero :=
  result.terminal.wordEqual.trans
    (congrArg Encoding.Encoder.Integral.CompleteEncoding.word result.terminal.encodingEq)

/-- The final projective terminal matrix reads the same original admitted proper-box sample. -/
theorem terminal_reading {trace : Basic.Trace Cursor.Question Reply} (result : Result trace) :
    Line.Gaussian.Proj.affineReading
      (Line.Matrix.act result.terminal.completion.state.matrix Line.Proj.omega) = result.admitted.realization.point :=
  result.terminal.reading.trans result.admitted.endpointPoint

/-- The same computed terminal word retains every old exposed word, including recalled occurrences. -/
theorem terminal_prefix {trace : Basic.Trace Cursor.Question Reply} (result : Result trace) :
    ∀ entry ∈ trace, entry.reply.word.IsPrefix result.terminal.completion.word := by
  intro entry member
  have retained : entry.reply.word.IsPrefix result.admitted.endpoint.cursor.word :=
    result.admitted.endpointValid.wordEq ▸ result.admitted.endpointPrefix entry member
  rcases retained with ⟨earlier, earlierEq⟩
  rcases result.terminal.wordPrefix with ⟨later, laterEq⟩
  exact ⟨earlier ++ later, (Data.List.Append.append_assoc _ earlier later).symm.trans
    ((congrArg (fun retainedWord => retainedWord ++ later) earlierEq).trans laterEq)⟩

/-- The canonical finite-history interpreter returns every original recorded and recalled complete reply exactly. -/
theorem answers {trace : Basic.Trace Cursor.Question Reply} (result : Result trace) :
    Basic.Answers (result.history.interpret result.valid) trace := by
  intro entry member
  have covered : entry ∈ result.history.trace := result.historyEq.symm ▸ result.admitted.covered entry member
  exact result.history.answers result.valid entry covered

/-- The canonical finite history retains the same explicit rational survivor of the original proper enclosure. -/
theorem pointEq {trace : Basic.Trace Cursor.Question Reply} (result : Result trace) :
    result.history.initial.point = result.admitted.realization.point :=
  (congrArg (fun history : History => history.initial.point) result.historyEq).trans result.admitted.historyPoint

/-- Canonical rational continuation preserves the complete adaptive execution of its original admitted trace. -/
theorem same_execution {trace : Basic.Trace Cursor.Question Reply} (result : Result trace)
    {Value : Type} (protocol : Protocol Cursor.Question Reply Value) (oracle : Cursor.Question → Reply)
    (traceEq : (protocol.run oracle).trace = trace) :
    protocol.run (result.history.interpret result.valid) = protocol.run oracle := by
  apply protocol.run_of_answers
  intro entry member
  exact result.answers entry (traceEq ▸ member)

end Result

end Purelib.Approximation.Gaussian.Observation.Prefix.Continuation

end
