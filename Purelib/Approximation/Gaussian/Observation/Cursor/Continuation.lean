module

public import Purelib.Approximation.Gaussian.Observation.Cursor.Source
public import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.History
import Purelib.Computation.Query.Path
import Purelib.Approximation.Gaussian.Observation.Cursor.Request
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.List.Append
import Purelib.Data.List.Membership

/-!
# Finite rational mixed-cursor continuation code

Code retains one rational reading, a complete numerical reply and its actual
local rational tail. The fixed interpreter restores that tail's exact mode
and consumes the saved words and chart caches. Later requests use the owned
productive controller and return certified finite code for the same reading.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Cursor.Continuation

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Computation
open Purelib.Computation.Query
open Purelib.Geometry.Projective

namespace Code

/-- Restore the same finite cursor at its exact tail, reusing its retained parser and all chart caches. -/
@[expose] def snapshot (code : Code) (valid : Valid code) : Machine.Snapshot :=
  Machine.Snapshot.ofFrame ((code.reply.atTail code.tail).frame valid.cursor)
    ((code.reply.atTail code.tail).grammar valid.cursor)

/-- Interpret finite code as a cached cursor state using only the fixed exact-tail process constructor. -/
@[expose] def state (code : Code) (valid : Valid code) : Source.State (code.snapshot valid) :=
  let history := Machine.History.start (code.snapshot valid)
  have currentMatrix : history.current.frame.matrix = code.reply.cursor.matrix :=
    (congrArg (fun snapshot : Machine.Snapshot => snapshot.frame.matrix)
      (Machine.History.start_current (code.snapshot valid))).trans
        ((code.reply.atTail code.tail).frame_caches valid.cursor).2.2.1
  Source.State.withCoefficient history code.reply.coefficient
    (valid.numerical.coefficientEq.trans (congrArg Chordal.Transport.transportCoefficient currentMatrix.symm))

/-- The restored current reply retains the code's exact exposed word. -/
theorem state_word (code : Code) (valid : Valid code) :
    (code.state valid).reply.cursor.emitted = code.reply.cursor.emitted :=
  congrArg (fun snapshot : Machine.Snapshot => snapshot.machine.emitted)
    (Machine.History.start_current (code.snapshot valid))

/-- The fixed finite-code interpreter has the same exact singleton rational origin for all future requests. -/
theorem exactCursor (code : Code) (valid : Valid code) :
    Machine.Semantics.Basic.ExactCursor (Process.exact code.point) () (code.snapshot valid).machine :=
  valid.candidate.exactCursor

end Code

set_option genInjectivity false in
/-- One finite-code request retains its new code, validity, fixed reading and complete numerical payment. -/
structure RequestResult (earlier : Code) (request : Request) where
  /-- The actual next finite cursor code computed by the fixed interpreter. -/ next : Code
  /-- The computed next code is numerically and geometrically valid. -/ valid : Valid next
  /-- The continuation retains its same fixed Gaussian-rational reading. -/ pointEq : next.point = earlier.point
  /-- The exact previously exposed word persists through the request. -/ wordPrefix :
    earlier.reply.cursor.emitted.IsPrefix next.reply.cursor.emitted
  /-- A prefix request returns its supplied additional finite count. -/ length :
    ∀ count, request = .bits count →
      next.reply.cursor.emitted.length = earlier.reply.cursor.emitted.length + count
  /-- An enclosure request meets its supplied strict squared-chordal target. -/ accurate :
    ∀ target positive, request = .enclosure target positive → next.reply.allowanceSq < target

namespace Code

/-- Answer a later mixed request from finite code and retain the same rational reading and exact saved prefix.

The interpreter calls only the fixed exact-tail controller. Its next local
tail and image come from that actual executed state; original source states
and callbacks are absent. All restored chart matrices are the saved caches.
-/
def request (code : Code) (valid : Valid code) (request : Request) : RequestResult code request := by
  let result := Source.request (code.state valid) request
  let history := result.next.history
  let survivor := history.survive
  let reading := survivor.read (code.exactCursor valid)
  have pointEq : reading.value = code.point := reading.originalPossible
  let realization := history.realize history.current history.currentMember
    survivor.tail survivor.possible survivor.image survivor.imageEq
  let candidate := Reply.ofRealization realization
  let affineCandidate : Reply.Candidate (Reply.ofSnapshot history.current) (Line.Proj.affine reading.value) :=
    ⟨candidate.tail, candidate.valid, candidate.inside, by
      change (Line.Proj.affine reading.value).Equivalent
        (history.current.frame.image (Reply.ofRealization realization).tail)
      rewrite [Reply.ofRealization_tail]
      exact Line.Proj.Equivalent.symm (reading.snapshot_represented realization)⟩
  let finalCandidate : Reply.Candidate result.next.reply (Line.Proj.affine code.point) :=
    result.next.replyEq.symm ▸ (pointEq ▸ affineCandidate)
  let certified := ofCandidate code.point result.next.reply finalCandidate result.next.numerical
  exact
    { next := certified.val
      valid := certified.property
      pointEq := rfl
      wordPrefix := (code.state_word valid) ▸ result.wordPrefix
      length := by
        intro count same
        exact (code.state_word valid) ▸ result.length count same
      accurate := result.accurate }

/-- Interpret an arbitrary finite later mixed request path, consuming each preceding certified finite code. -/
def execute : (code : Code) → Valid code → List Request → {next : Code // Valid next}
  | code, valid, [] => ⟨code, valid⟩
  | code, valid, request :: rest =>
      let result := code.request valid request
      execute result.next result.valid rest

/-- Every finite later mixed execution retains the exact same Gaussian-rational reading. -/
theorem execute_point (code : Code) (valid : Valid code) (requests : List Request) :
    (code.execute valid requests).val.point = code.point := by
  induction requests generalizing code with
  | nil => rfl
  | cons request rest induction =>
      exact (induction (code.request valid request).next (code.request valid request).valid).trans
        (code.request valid request).pointEq

end Code

/-- Retain the same valid current code and exact unconsumed certified saved suffix. -/
abbrev State := Query.History.State Continuation.Valid Step.Valid

namespace State

set_option genInjectivity false in
/-- An interpreted request retains its complete payment and the same next code's remaining saved chain. -/
structure Result (earlier : State) (request : Request) where
  /-- The actual next finite code and complete prefix or accuracy certificate. -/ result :
    RequestResult earlier.code request
  /-- The exact unconsumed saved suffix on the resulting path. -/ remaining : List Step
  /-- The suffix begins at that same computed or retained next code. -/ chain : Chain result.next remaining

namespace Result

/-- Project the exact next code and remaining saved suffix without repeating any request. -/
@[expose] def state {earlier : State} {request : Request} (result : Result earlier request) : State :=
  ⟨result.result.next, result.result.valid, result.remaining, result.chain⟩

end Result

/-- Interpret a request using its matching saved transition or the same current finite rational cursor.

A different request leaves the saved path permanently. Its fallback starts
at the exact current code, so all later requests preserve the actually exposed
prefix and the same rational reading instead of overlaying unrelated replies.
-/
def request (state : State) (request : Request) : Result state request := by
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
          length := by intro count requested; exact head.length count (same.symm.trans requested)
          accurate := by
            intro target positive requested
            exact head.accurate target positive (same.symm.trans requested) }
      exact ⟨result, remaining, chain.tail⟩

/-- Consume one interpreted request's same next code and saved suffix. -/
def step (state : State) (request : Request) : State := (state.request request).state

/-- A matching saved request retains the exact cached next code and remaining suffix. -/
private theorem step_saved_specification (code : Code) (valid : Valid code) (saved : Step) (remaining : List Step)
    (chain : Chain code (saved :: remaining)) :
    step (Query.History.State.mk code valid (saved :: remaining) chain) saved.request =
      Query.History.State.mk saved.next chain.head.nextValid remaining chain.tail := by
  unfold step request Query.History.State.select
  dsimp only
  rewrite [dif_pos rfl]
  rfl

/-- A matching saved request uses its original complete finite code without invoking the fallback controller. -/
theorem step_saved (code : Code) (valid : Valid code) (saved : Step) (remaining : List Step)
    (chain : Chain code (saved :: remaining)) :
    step (Query.History.State.mk code valid (saved :: remaining) chain) saved.request =
      Query.History.State.mk saved.next chain.head.nextValid remaining chain.tail :=
  step_saved_specification code valid saved remaining chain

/-- Every interpreted request retains the same rational reading on saved and divergent paths. -/
private theorem step_point_specification (state : State) (request : Request) :
    (state.step request).code.point = state.code.point := (state.request request).result.pointEq

/-- The interpreted saved or future transition retains its exact fixed rational reading. -/
theorem step_point (state : State) (request : Request) :
    (state.step request).code.point = state.code.point := step_point_specification state request

/-- The interpreted state projection retains its original request's complete prefix and accuracy certificates. -/
private theorem step_payment_specification (state : State) (request : Request) :
    state.code.reply.cursor.emitted.IsPrefix (state.step request).code.reply.cursor.emitted ∧
      (∀ count, request = .bits count →
        (state.step request).code.reply.cursor.emitted.length = state.code.reply.cursor.emitted.length + count) ∧
      (∀ target positive, request = .enclosure target positive →
        (state.step request).code.reply.allowanceSq < target) :=
  ⟨(state.request request).result.wordPrefix, (state.request request).result.length,
    (state.request request).result.accurate⟩

/-- Every saved or later interpreted request extends the exact previously exposed word. -/
theorem step_prefix (state : State) (request : Request) :
    state.code.reply.cursor.emitted.IsPrefix (state.step request).code.reply.cursor.emitted :=
  (step_payment_specification state request).1

/-- Every saved or later bit request pays its exact additional count. -/
theorem step_length (state : State) (count : Nat) :
    (state.step (.bits count)).code.reply.cursor.emitted.length = state.code.reply.cursor.emitted.length + count :=
  (step_payment_specification state (.bits count)).2.1 count rfl

/-- Every saved or later enclosure request pays its original strict positive target. -/
theorem step_accurate (state : State) (target : Fraction.Rational) (positive : 0 < target) :
    (state.step (.enclosure target positive)).code.reply.allowanceSq < target :=
  (step_payment_specification state (.enclosure target positive)).2.2 target positive rfl

/-- Execute the same finite path, consuming saved transitions while its requests continue to match. -/
@[expose] def execute : State → List Request → State := Query.History.execute step

/-- Appending a request path continues from its actual previously interpreted state. -/
theorem execute_append (state : State) (earlier later : List Request) :
    state.execute (earlier ++ later) = (state.execute earlier).execute later :=
  Query.History.execute_append step state earlier later

/-- Every finite saved or divergent request path retains the same exact rational reading. -/
theorem execute_point (state : State) (requests : List Request) :
    (state.execute requests).code.point = state.code.point :=
  Query.History.execute_reading step (fun state : State => state.code.point) step_point state requests

/-- Answer a full original path question from this same finite rational history state. -/
@[expose] def answer (state : State) (question : Question) : Reply := (state.execute question.path).code.reply

/-- Every saved exchange is reproduced exactly after its actual preceding path has been interpreted. -/
theorem answers_from (start : State) (path : List Request) (code : Code) (valid : Valid code)
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

/-- Answer mixed numerical path questions using only finite history code and its fixed rational cursor interpreter. -/
@[expose] def interpret (history : History) (valid : History.Valid history) : Question → Reply :=
  (history.state valid).answer

/-- Finite history code reproduces every original saved complete numerical reply. -/
theorem answers (history : History) (valid : History.Valid history) :
    Basic.Answers (history.interpret valid) history.trace :=
  State.answers_from (history.state valid) [] history.initial valid.initial history.steps valid.chain rfl

/-- Every interpreted historical or future reply is numerical at its retained chart and allowance. -/
theorem interpret_numerical (history : History) (valid : History.Valid history) (question : Question) :
    Reply.Numerical (history.interpret valid question) :=
  ((history.state valid).execute question.path).valid.numerical

/-- Every interpreted historical or future reply has a certified candidate at the history's same rational reading. -/
def interpret_candidate (history : History) (valid : History.Valid history) (question : Question) :
    Reply.Candidate (history.interpret valid question) (Line.Proj.affine history.initial.point) :=
  ((history.state valid).execute_point question.path) ▸
    ((history.state valid).execute question.path).valid.candidate

/-- The interpreted reply extends the exact word at its actual preceding path, including paths leaving saved history. -/
theorem interpret_prefix (history : History) (valid : History.Valid history) (question : Question) :
    ((history.state valid).execute question.previous).code.reply.cursor.emitted.IsPrefix
      (history.interpret valid question).cursor.emitted := by
  have extension := ((history.state valid).execute question.previous).step_prefix question.request
  change ((history.state valid).execute question.previous).code.reply.cursor.emitted.IsPrefix
    ((history.state valid).execute question.path).code.reply.cursor.emitted
  unfold Question.path Path.Question.path
  rewrite [State.execute_append]
  exact extension

/-- Every additional-bit question receives its exact requested length on historical and divergent paths. -/
theorem interpret_length (history : History) (valid : History.Valid history) (previous : List Request) (count : Nat) :
    (history.interpret valid ⟨previous, .bits count⟩).cursor.emitted.length =
      ((history.state valid).execute previous).code.reply.cursor.emitted.length + count := by
  change ((history.state valid).execute (previous ++ [.bits count])).code.reply.cursor.emitted.length = _
  rewrite [State.execute_append]
  exact ((history.state valid).execute previous).step_length count

/-- Every positive enclosure question receives its strict target allowance on historical and divergent paths. -/
theorem interpret_accurate (history : History) (valid : History.Valid history) (previous : List Request)
    (target : Fraction.Rational) (positive : 0 < target) :
    (history.interpret valid ⟨previous, .enclosure target positive⟩).allowanceSq < target := by
  change ((history.state valid).execute (previous ++ [.enclosure target positive])).code.reply.allowanceSq < target
  rewrite [State.execute_append]
  exact ((history.state valid).execute previous).step_accurate target positive

end History

set_option genInjectivity false in
/-- A mixed transcript retains its original admission and the same certified finite rational history code. -/
structure Result (trace : Basic.Trace Question Reply) where
  /-- The original joint numerical admission and cached realizations. -/ admitted : Admitted trace
  /-- The actual finite rational history used by the answering interpreter. -/ history : History
  /-- The interpreter consumes the exact original admission's cached history. -/ historyEq : history = admitted.history
  /-- The same retained finite history is valid. -/ valid : history.Valid

/-- Construct the whole-history mixed continuation by retaining the admission's exact finite data and certificates. -/
def ofAdmitted {trace : Basic.Trace Question Reply} (admitted : Admitted trace) : Result trace :=
  ⟨admitted, admitted.history, rfl, admitted.historyValid⟩

namespace Result

/-- The finite history interpreter returns exactly every original recorded or recalled complete reply. -/
theorem answers {trace : Basic.Trace Question Reply} (result : Result trace) :
    Basic.Answers (result.history.interpret result.valid) trace := by
  intro entry member
  have covered : entry ∈ result.history.trace := result.historyEq.symm ▸ result.admitted.covered entry member
  exact result.history.answers result.valid entry covered

/-- The whole-history continuation retains the admission's same explicitly computed rational reading. -/
theorem pointEq {trace : Basic.Trace Question Reply} (result : Result trace) :
    result.history.initial.point = result.admitted.point :=
  (congrArg (fun history : History => history.initial.point) result.historyEq).trans result.admitted.historyPoint

/-- Every historical or future reply has its certified candidate at the same original admitted rational reading. -/
def candidate {trace : Basic.Trace Question Reply} (result : Result trace) (question : Question) :
    Reply.Candidate (result.history.interpret result.valid question) (Line.Proj.affine result.admitted.point) :=
  result.pointEq ▸ result.history.interpret_candidate result.valid question

/-- Whole-history mixed rational replacement preserves the exact adaptive execution of a protocol with this trace. -/
theorem same_execution {trace : Basic.Trace Question Reply} (result : Result trace)
    {Value : Type} (protocol : Protocol Question Reply Value) (oracle : Question → Reply)
    (traceEq : (protocol.run oracle).trace = trace) :
    protocol.run (result.history.interpret result.valid) = protocol.run oracle := by
  apply protocol.run_of_answers
  intro entry member
  exact result.answers entry (traceEq ▸ member)

end Result

end Purelib.Approximation.Gaussian.Observation.Cursor.Continuation

end
