module

public import Purelib.Approximation.Gaussian.Observation.Cursor.Transcript
import Purelib.Computation.Query.Path
import Purelib.Approximation.Gaussian.Observation.Cursor.Request
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership

open Purelib.Data.CCL.Transducer.Machine.History.Survivor

/-!
# Actual mixed numerical requests on retained productive cursor histories

The source state keeps its original executed history and exact cached current
reply. Bit requests advance that same cursor; enclosure requests consume the
cached positive chart coefficient and refine its actual local mode once.
The reply after refinement reuses the same coefficient and chart caches.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Cursor.Source

open Purelib
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.Rat
open Purelib.Computation.Query
open Purelib.Geometry.Projective

set_option genInjectivity false in
/-- The actual original mixed-request source retains its executed history and complete current numerical reply. -/
structure State (initial : Machine.Snapshot) where
  /-- The actual original cached cursor history. -/ history : Machine.History initial
  /-- The exact finite current numerical reply, computed once. -/ reply : Reply
  /-- The reply belongs to the actual same current checkpoint. -/ replyEq : reply = Reply.ofSnapshot history.current

namespace State

/-- Read cumulative original supplied-source work from this same retained productive history. -/
@[expose] def sourceCalls {initial : Machine.Snapshot} (state : State initial) : Nat :=
  state.history.sourceCalls

/-- Prepare an original mixed-request source with its current numerical reply cached once. -/
@[expose] def ofHistory {initial : Machine.Snapshot} (history : Machine.History initial) : State initial :=
  let reply := Reply.ofSnapshot history.current
  ⟨history, reply, rfl⟩

/-- Prepare a current state using its already cached correct chart coefficient. -/
@[expose] def withCoefficient {initial : Machine.Snapshot} (history : Machine.History initial)
    (coefficient : Fraction.Rational)
    (coefficientEq : coefficient = Chordal.Transport.transportCoefficient history.current.frame.matrix) :
    State initial :=
  ⟨history, Reply.withCoefficient history.current coefficient,
    Reply.withCoefficient_eq history.current coefficient coefficientEq⟩

/-- The actual cached reply has its retained positive coefficient and correct squared-chordal allowance. -/
theorem numerical {initial : Machine.Snapshot} (state : State initial) : Reply.Numerical state.reply :=
  state.replyEq.symm ▸ Reply.ofSnapshot_numerical state.history.current

end State

set_option genInjectivity false in
/-- An actual request returns its same retained next state and complete numerical prefix or accuracy certificate. -/
structure Result {initial : Machine.Snapshot} (before : State initial) (request : Request) where
  /-- The actual same original source after the finite request. -/ next : State initial
  /-- Every earlier actual checkpoint remains available for the same later witness. -/ earlier :
    ∀ snapshot ∈ before.history.snapshots, snapshot ∈ next.history.snapshots
  /-- Every request retains the exact previously exposed word as a prefix. -/ wordPrefix :
    before.reply.cursor.emitted.IsPrefix next.reply.cursor.emitted
  /-- A bit request returns exactly the supplied additional bit count. -/ length :
    ∀ count, request = .bits count →
      next.reply.cursor.emitted.length = before.reply.cursor.emitted.length + count
  /-- An enclosure request pays its actual strict squared-chordal target. -/ accurate :
    ∀ target positive, request = .enclosure target positive → next.reply.allowanceSq < target

/-- Execute an actual finite prefix or charted-enclosure request using the same current caches. -/
def request {initial : Machine.Snapshot} (before : State initial) (request : Request) : Result before request := by
  cases request with
  | bits count =>
      let history := before.history.advance count
      let next := State.ofHistory history
      have extension := before.history.advance_word count
      have replyWord : before.reply.cursor.emitted = before.history.current.machine.emitted :=
        congrArg (fun reply => reply.cursor.emitted) before.replyEq
      exact
        { next := next
          earlier := before.history.advance_earlier count
          wordPrefix := replyWord.symm ▸ extension.1
          length := by intro requested same; cases same; exact replyWord.symm ▸ extension.2
          accurate := by intro _ _ impossible; nomatch impossible }
  | enclosure target positive =>
      let coefficient := before.reply.coefficient
      have coefficientPositive : 0 < coefficient := before.numerical.coefficientPositive
      have scalePositive : 0 < 4 * coefficient :=
        Fraction.Order.Arithmetic.mul_pos_direct (by decide) coefficientPositive
      let ballTarget := target / (4 * coefficient)
      have ballTargetPositive : 0 < ballTarget := Fraction.Order.Field.div_pos_direct positive scalePositive
      let history := before.history.refine ballTarget ballTargetPositive
      let reply := Reply.withCoefficient history.current coefficient
      have coefficientEq : coefficient = Chordal.Transport.transportCoefficient history.current.frame.matrix := by
        have oldEq := congrArg (fun reply => reply.cursor.matrix) before.replyEq
        exact (before.numerical.coefficientEq.trans
          (congrArg Chordal.Transport.transportCoefficient oldEq)).trans
            (congrArg Chordal.Transport.transportCoefficient
              (before.history.refine_matrix ballTarget ballTargetPositive).symm)
      let next := State.withCoefficient history coefficient coefficientEq
      have wordEq : next.reply.cursor.emitted = before.reply.cursor.emitted :=
        (before.history.refine_words ballTarget ballTargetPositive).1.trans
          (congrArg (fun reply => reply.cursor.emitted) before.replyEq).symm
      have accurate : next.reply.allowanceSq < target := by
        have scaled := (Fraction.Order.Field.lt_div_iff_pos scalePositive).mp
          (before.history.refine_accurate ballTarget ballTargetPositive)
        change (4 * coefficient) * history.current.ball.radiusSq < target
        have commute : history.current.ball.radiusSq * (4 * coefficient) =
            (4 * coefficient) * history.current.ball.radiusSq := Fraction.Field.mul_comm _ _
        exact commute ▸ scaled
      exact
        { next := next
          earlier := before.history.refine_earlier ballTarget ballTargetPositive
          wordPrefix := ⟨[], (Data.List.Append.append_nil _).trans wordEq.symm⟩
          length := by intro _ impossible; nomatch impossible
          accurate := by intro requested requestedPositive same; cases same; exact accurate }

/-- An actual mixed request retains all earlier supplied-source work. -/
theorem request_sourceCalls_mono {initial : Machine.Snapshot} (before : State initial) (next : Request) :
    before.sourceCalls ≤ (request before next).next.sourceCalls := by
  cases next with
  | bits count => exact before.history.advance_sourceCalls_mono count
  | enclosure target positive =>
      change before.history.sourceCalls ≤
        (before.history.refine (target / (4 * before.reply.coefficient)) _).sourceCalls
      rewrite [Machine.History.refine_sourceCalls]
      exact Nat.le_add_right _ 3

/-- A bit request pays at most the actual seven-call inverse transition per requested bit.

Buffered bits reuse the same observation and pay zero. This upper bound does
not identify bits with source calls; the returned history retains its exact
actual branch costs.
-/
theorem request_bits_sourceCalls_le {initial : Machine.Snapshot} (before : State initial) (count : Nat) :
    (request before (.bits count)).next.sourceCalls ≤ before.sourceCalls + 7 * count :=
  before.history.advance_sourceCalls_le count

/-- An explicit enclosure request adds one routed refinement and its same cached ball and witness reads. -/
theorem request_enclosure_sourceCalls {initial : Machine.Snapshot} (before : State initial)
    (target : Fraction.Rational) (positive : 0 < target) :
    (request before (.enclosure target positive)).next.sourceCalls = before.sourceCalls + 3 :=
  before.history.refine_sourceCalls (target / (4 * before.reply.coefficient)) _

namespace State

/-- Execute an original mixed request path using each same actual cached current state. -/
@[expose] def execute {initial : Machine.Snapshot} : State initial → List Request → State initial
  | state, [] => state
  | state, next :: rest => execute (Source.request state next).next rest

/-- The original request path continues from the actual earlier retained state at an append boundary. -/
theorem execute_append {initial : Machine.Snapshot} (state : State initial) (earlier later : List Request) :
    state.execute (earlier ++ later) = (state.execute earlier).execute later := by
  induction earlier generalizing state with
  | nil => rfl
  | cons next rest induction => exact induction _

/-- The actual finite request path retains every original source call already paid by its starting history. -/
theorem execute_sourceCalls_mono {initial : Machine.Snapshot} (state : State initial) (requests : List Request) :
    state.sourceCalls ≤ (state.execute requests).sourceCalls := by
  induction requests generalizing state with
  | nil => exact Nat.le_refl _
  | cons next rest induction => exact (request_sourceCalls_mono state next).trans (induction _)

end State

/-- Answer a finite path question by the exact original mixed-request procedure. -/
@[expose] def answer {initial : Machine.Snapshot} (state : State initial) (question : Question) : Reply :=
  (Source.request (state.execute question.previous) question.request).next.reply

set_option genInjectivity false in
/-- A recorded numerical occurrence retains its original question, snapshot and exact cached complete reply. -/
structure Occurrence {initial : Machine.Snapshot} (origin : State initial) where
  /-- The actual finite path question asked at this occurrence. -/ question : Question
  /-- The actual original checkpoint supplying this same reply. -/ snapshot : Machine.Snapshot
  /-- The exact returned finite numerical reply. -/ reply : Reply
  /-- The reply belongs to that same original checkpoint. -/ replyEq : reply = Reply.ofSnapshot snapshot
  /-- The cached reply is the original path adapter's actual answer. -/ answerEq : reply = answer origin question
  /-- The exact word exposed at the original preceding state. -/ previousWord : List Bool
  /-- The original request extends that exact previously exposed word. -/ wordPrefix :
    previousWord.IsPrefix reply.cursor.emitted
  /-- A bit request pays its actual additional length. -/ length :
    ∀ count, question.request = .bits count → reply.cursor.emitted.length = previousWord.length + count
  /-- The original charted-enclosure request pays its strict numerical target. -/ accurate :
    ∀ target positive, question.request = .enclosure target positive → reply.allowanceSq < target

namespace Occurrence

/-- Read the exact original numerical exchange without rereading its source or chart. -/
@[expose] def exchange {initial : Machine.Snapshot} {origin : State initial} (occurrence : Occurrence origin) :
    Basic.Exchange Question Reply := ⟨occurrence.question, occurrence.reply⟩

end Occurrence

set_option genInjectivity false in
/-- The actual new requests form one chronological path from their exact preceding numerical replies. -/
inductive Spine {initial : Machine.Snapshot} (origin : State initial) :
    List Request → Reply → List (Occurrence origin) → List Request → Reply → Prop where
  /-- An empty actual path retains the same numerical reply. -/ | nil (path : List Request) (reply : Reply) :
      Spine origin path reply [] path reply
  /-- One actual occurrence consumes the preceding path and exact exposed word. -/ | cons
      (occurrence : Occurrence origin) (path : List Request) (reply : Reply)
      (questionEq : occurrence.question.previous = path)
      (wordEq : occurrence.previousWord = reply.cursor.emitted)
      {remaining : List (Occurrence origin)} {endPath : List Request} {endReply : Reply}
      (tail : Spine origin occurrence.question.path occurrence.reply remaining endPath endReply) :
      Spine origin path reply (occurrence :: remaining) endPath endReply

namespace Spine

/-- Each actual new request occurrence extends the original finite path by one. -/
theorem length_path {initial : Machine.Snapshot} {origin : State initial}
    {path : List Request} {reply : Reply} {occurrences : List (Occurrence origin)}
    {endPath : List Request} {endReply : Reply} (spine : Spine origin path reply occurrences endPath endReply) :
    endPath.length = path.length + occurrences.length := by
  induction spine with
  | nil path _ => exact (Nat.add_zero path.length).symm
  | cons occurrence path reply questionEq wordEq tail induction =>
      have questionLength : occurrence.question.path.length = path.length + 1 := by
        change (occurrence.question.previous ++ [_]).length = _
        rewrite [Data.List.Append.length_append, questionEq]
        rfl
      exact induction.trans ((congrArg (fun count => count + _) questionLength).trans
        ((Nat.add_assoc _ _ _).trans
          (congrArg (fun count => path.length + count) (Nat.add_comm _ _))))

/-- Append an actual new occurrence at the exact current path and numerical reply. -/
theorem append {initial : Machine.Snapshot} {origin : State initial}
    {path : List Request} {reply : Reply} {occurrences : List (Occurrence origin)}
    {endPath : List Request} {endReply : Reply} (spine : Spine origin path reply occurrences endPath endReply)
    (occurrence : Occurrence origin) (questionEq : occurrence.question.previous = endPath)
    (wordEq : occurrence.previousWord = endReply.cursor.emitted) :
    Spine origin path reply (occurrences ++ [occurrence]) occurrence.question.path occurrence.reply := by
  induction spine with
  | nil path reply => exact .cons occurrence path reply questionEq wordEq (.nil _ _)
  | cons earlier path reply earlierQuestion earlierWord tail induction =>
      exact .cons earlier path reply earlierQuestion earlierWord (induction questionEq wordEq)

end Spine

set_option genInjectivity false in
/-- An actual mixed-request recording keeps its source state, path, original occurrences and exact ordered trace. -/
structure Recording {initial : Machine.Snapshot} (origin : State initial) where
  /-- The same retained original source state after the actual request path. -/ current : State initial
  /-- The actual path of newly executed mixed requests. -/ path : List Request
  /-- The state is the original procedure's result on that same path. -/ stateEq : current = origin.execute path
  /-- The original numerical occurrences in order, including recalled ones. -/ occurrences : List (Occurrence origin)
  /-- The same new request occurrences in order, before adding any recalled repetitions. -/ spine :
    List (Occurrence origin)
  /-- The actual new requests bind each original question and word to the exact preceding reply. -/ spineEq :
    Spine origin [] origin.reply spine path current.reply
  /-- Every new request occurrence is retained in the complete ordered recording. -/ spineIncluded :
    ∀ occurrence ∈ spine, occurrence ∈ occurrences
  /-- Every recorded or recalled occurrence belongs to the same actual new-request spine. -/ covered :
    ∀ occurrence ∈ occurrences, occurrence ∈ spine
  /-- The original starting checkpoint remains in the actual current history. -/ originRetained :
    origin.history.current ∈ current.history.snapshots
  /-- The exact ordered numerical exchanges, cached once. -/ trace : Basic.Trace Question Reply
  /-- The trace consists of these same retained actual occurrences. -/ traceEq :
    trace = occurrences.map Occurrence.exchange
  /-- Every original occurrence's checkpoint remains in the actual current history. -/ retained :
    ∀ occurrence ∈ occurrences, occurrence.snapshot ∈ current.history.snapshots

namespace Recording

/-- Count actual new handler invocations from their retained chronological spine, excluding recalls. -/
@[expose] def requestCount {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) : Nat := recording.spine.length

/-- Actual new handler invocations are exactly the length of this recording's original request path. -/
theorem requestCount_eq {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) : recording.requestCount = recording.path.length :=
  (recording.spineEq.length_path.trans (Nat.zero_add _)).symm

/-- Read all original supplied-source calls retained by the current history, including work before this recording. -/
@[expose] def sourceCalls {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) : Nat := recording.current.sourceCalls

/-- Every recording preserves the cumulative original work already retained at its starting state. -/
theorem sourceCalls_mono {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) : origin.sourceCalls ≤ recording.sourceCalls := by
  change origin.sourceCalls ≤ recording.current.sourceCalls
  rewrite [recording.stateEq]
  exact origin.execute_sourceCalls_mono recording.path

/-- Read only the actual additional supplied-source work after this recording's original starting history. -/
@[expose] def sourceCallsSinceStart {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) : Nat := recording.sourceCalls - origin.sourceCalls

/-- Earlier retained work plus the actual new work equals this same history's cumulative source payment. -/
theorem sourceCalls_accounted {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) : origin.sourceCalls + recording.sourceCallsSinceStart = recording.sourceCalls :=
  Nat.add_sub_of_le recording.sourceCalls_mono

/-- Start a mixed recording with its actual cached initial source and empty path and trace. -/
def start {initial : Machine.Snapshot} (origin : State initial) : Recording origin :=
  { current := origin
    path := []
    stateEq := rfl
    occurrences := []
    spine := []
    spineEq := .nil [] origin.reply
    spineIncluded := fun _ impossible => by nomatch impossible
    covered := fun _ impossible => by nomatch impossible
    originRetained := origin.history.currentMember
    trace := []
    traceEq := rfl
    retained := fun _ impossible => by nomatch impossible }

/-- The recording constructor starts with an empty actual path and ordered trace. -/
private theorem start_specification {initial : Machine.Snapshot} (origin : State initial) :
    (start origin).path = [] ∧ (start origin).trace = [] := ⟨rfl, rfl⟩

/-- A newly started recording has no source requests in its actual path. -/
theorem start_path {initial : Machine.Snapshot} (origin : State initial) :
    (start origin).path = [] := (start_specification origin).1

/-- A newly started recording has an empty ordered numerical trace. -/
theorem start_trace {initial : Machine.Snapshot} (origin : State initial) :
    (start origin).trace = [] := (start_specification origin).2

/-- The original starting constructor retains its same history's paid-call field. -/
private theorem start_sourceCalls_specification {initial : Machine.Snapshot} (origin : State initial) :
    (start origin).sourceCalls = origin.sourceCalls := rfl

/-- Starting a recording preserves its supplied history's cumulative payment without making another source call. -/
theorem start_sourceCalls {initial : Machine.Snapshot} (origin : State initial) :
    (start origin).sourceCalls = origin.sourceCalls := start_sourceCalls_specification origin

/-- A new recording retains no new handler invocation or additional source work. -/
theorem start_work {initial : Machine.Snapshot} (origin : State initial) :
    (start origin).requestCount = 0 ∧ (start origin).sourceCallsSinceStart = 0 :=
  ⟨rfl, Nat.sub_self _⟩

/-- Execute one actual mixed request once and append its cached reply and original checkpoint to the recording. -/
def request {initial : Machine.Snapshot} {origin : State initial} (recording : Recording origin) (next : Request) :
    Recording origin := by
  let result := Source.request recording.current next
  let question : Question := ⟨recording.path, next⟩
  have resultEq : result.next = (Source.request (origin.execute recording.path) next).next :=
    congrArg (fun state => (Source.request state next).next) recording.stateEq
  let occurrence : Occurrence origin :=
    ⟨question, result.next.history.current, result.next.reply, result.next.replyEq,
      congrArg State.reply resultEq, recording.current.reply.cursor.emitted,
      result.wordPrefix, result.length, result.accurate⟩
  have stateEq : result.next = origin.execute (recording.path ++ [next]) := by
    rewrite [State.execute_append]
    exact resultEq
  have traceEq : recording.trace ++ [occurrence.exchange] =
      (recording.occurrences ++ [occurrence]).map Occurrence.exchange := by
    rewrite [Data.List.Map.map_append]
    exact congrArg (fun earlier => earlier ++ [occurrence.exchange]) recording.traceEq
  exact
    { current := result.next
      path := recording.path ++ [next]
      stateEq := stateEq
      occurrences := recording.occurrences ++ [occurrence]
      spine := recording.spine ++ [occurrence]
      spineEq := recording.spineEq.append occurrence rfl rfl
      spineIncluded := by
        intro entry included
        cases Data.List.Membership.mem_append.mp included with
        | inl earlier => exact Data.List.Membership.mem_append.mpr (.inl (recording.spineIncluded entry earlier))
        | inr final => exact Data.List.Membership.mem_append.mpr (.inr final)
      covered := by
        intro entry included
        cases Data.List.Membership.mem_append.mp included with
        | inl earlier => exact Data.List.Membership.mem_append.mpr (.inl (recording.covered entry earlier))
        | inr final => exact Data.List.Membership.mem_append.mpr (.inr final)
      originRetained := result.earlier origin.history.current recording.originRetained
      trace := recording.trace ++ [occurrence.exchange]
      traceEq := traceEq
      retained := by
        intro entry member
        cases Data.List.Membership.mem_append.mp member with
        | inl earlier => exact result.earlier entry.snapshot (recording.retained entry earlier)
        | inr final =>
            have equal := Data.List.Membership.mem_singleton.mp final
            cases equal
            exact result.next.history.currentMember }

/-- Recall one original numerical occurrence without advancing its source, changing its path or rereading its reply. -/
def recall {initial : Machine.Snapshot} {origin : State initial} (recording : Recording origin)
    (occurrence : Occurrence origin) (member : occurrence ∈ recording.occurrences) : Recording origin :=
  { current := recording.current
    path := recording.path
    stateEq := recording.stateEq
    occurrences := recording.occurrences ++ [occurrence]
    spine := recording.spine
    spineEq := recording.spineEq
    spineIncluded := fun entry included =>
      Data.List.Membership.mem_append.mpr (.inl (recording.spineIncluded entry included))
    covered := by
      intro entry included
      cases Data.List.Membership.mem_append.mp included with
      | inl earlier => exact recording.covered entry earlier
      | inr final =>
          have equal := Data.List.Membership.mem_singleton.mp final
          cases equal
          exact recording.covered occurrence member
    originRetained := recording.originRetained
    trace := recording.trace ++ [occurrence.exchange]
    traceEq := by
      rewrite [Data.List.Map.map_append]
      exact congrArg (fun earlier => earlier ++ [occurrence.exchange]) recording.traceEq
    retained := by
      intro entry included
      cases Data.List.Membership.mem_append.mp included with
      | inl earlier => exact recording.retained entry earlier
      | inr final =>
          have equal := Data.List.Membership.mem_singleton.mp final
          cases equal
          exact recording.retained occurrence member }

/-- A new actual request adds one handler invocation without charging recalled numerical exchanges. -/
theorem request_count {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (next : Request) :
    (recording.request next).requestCount = recording.requestCount + 1 :=
  Data.List.Append.length_append recording.spine _

/-- Each actual requested state retains the preceding history's exact cumulative supplied-source work. -/
theorem request_sourceCalls_mono {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (next : Request) :
    recording.sourceCalls ≤ (recording.request next).sourceCalls :=
  Source.request_sourceCalls_mono recording.current next

/-- A retained bit request has its same original finite upper bound on additional supplied-source calls. -/
theorem request_bits_sourceCalls_le {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (count : Nat) :
    (recording.request (.bits count)).sourceCalls ≤ recording.sourceCalls + 7 * count :=
  Source.request_bits_sourceCalls_le recording.current count

/-- An actual enclosure request adds exactly its original refinement and two cached source readings. -/
theorem request_enclosure_sourceCalls {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (target : Fraction.Rational) (positive : 0 < target) :
    (recording.request (.enclosure target positive)).sourceCalls = recording.sourceCalls + 3 :=
  Source.request_enclosure_sourceCalls recording.current target positive

/-- A recall reuses its exact original state and reply, adding neither a handler invocation nor source work. -/
theorem recall_work {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (occurrence : Occurrence origin) (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).requestCount = recording.requestCount ∧
      (recording.recall occurrence member).sourceCalls = recording.sourceCalls ∧
      (recording.recall occurrence member).sourceCallsSinceStart = recording.sourceCallsSinceStart :=
  ⟨rfl, rfl, rfl⟩

/-- The mixed request builder retains its exact path, appended exchange and original answer. -/
private theorem request_specification {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (next : Request) :
    (recording.request next).path = recording.path ++ [next] ∧
      (recording.request next).trace = recording.trace ++
        [⟨⟨recording.path, next⟩, (recording.request next).current.reply⟩] ∧
      (recording.request next).current.reply = answer origin ⟨recording.path, next⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  exact congrArg State.reply
    (congrArg (fun state => (Source.request state next).next) recording.stateEq)

/-- A new request extends the same original finite request path exactly. -/
theorem request_path {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (next : Request) :
    (recording.request next).path = recording.path ++ [next] := (request_specification recording next).1

/-- A new request appends the same actual cached complete reply at its original path question. -/
theorem request_trace {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (next : Request) :
    (recording.request next).trace = recording.trace ++
      [⟨⟨recording.path, next⟩, (recording.request next).current.reply⟩] :=
  (request_specification recording next).2.1

/-- The new recording's cached reply is exactly the original path adapter's answer. -/
theorem request_reply {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (next : Request) :
    (recording.request next).current.reply = answer origin ⟨recording.path, next⟩ :=
  (request_specification recording next).2.2

/-- Recalling an occurrence retains the original path and appends that same cached exchange. -/
private theorem recall_specification {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (occurrence : Occurrence origin) (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).path = recording.path ∧
      (recording.recall occurrence member).trace = recording.trace ++ [occurrence.exchange] := ⟨rfl, rfl⟩

/-- Recalling a saved occurrence leaves the actual source request path unchanged. -/
theorem recall_path {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (occurrence : Occurrence origin) (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).path = recording.path := (recall_specification recording occurrence member).1

/-- Recalling a saved occurrence appends its exact complete numerical exchange. -/
theorem recall_trace {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (occurrence : Occurrence origin) (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).trace = recording.trace ++ [occurrence.exchange] :=
  (recall_specification recording occurrence member).2

/-- Execute a finite requested mixed path by consuming each exact previously retained recording. -/
def execute {initial : Machine.Snapshot} {origin : State initial} : Recording origin → List Request → Recording origin
  | recording, [] => recording
  | recording, next :: rest => execute (recording.request next) rest

/-- Every recorded occurrence is the complete reply of the original finite path adapter. -/
theorem answers {initial : Machine.Snapshot} {origin : State initial} (recording : Recording origin) :
    Basic.Answers (answer origin) recording.trace := by
  intro entry member
  have mapped : entry ∈ recording.occurrences.map Occurrence.exchange := recording.traceEq ▸ member
  rcases Data.List.Map.mem_map.mp mapped with ⟨occurrence, _present, rfl⟩
  exact occurrence.answerEq.symm

/-- Realize one actual recorded occurrence from the same cached final image and its original inverse chart. -/
private def realizeOccurrence {initial : Machine.Snapshot} {origin : State initial} (recording : Recording origin)
    (survivor : Machine.History.Survivor recording.current.history) {process : Process} {state : process.State}
    (reading : Reading survivor process state) (occurrence : Occurrence origin)
    (member : occurrence ∈ recording.occurrences) : Realization occurrence.exchange reading.value := by
  let realization := recording.current.history.realize occurrence.snapshot (recording.retained occurrence member)
    survivor.tail survivor.possible survivor.image survivor.imageEq
  let candidate := Reply.ofRealization realization
  have represented : (Line.Proj.affine reading.value).Equivalent
      (Line.Matrix.act occurrence.snapshot.frame.matrix (Line.Proj.affine realization.value)) :=
    Line.Proj.Equivalent.symm (reading.snapshot_represented realization)
  let affineCandidate : Reply.Candidate (Reply.ofSnapshot occurrence.snapshot) (Line.Proj.affine reading.value) :=
    ⟨candidate.tail, candidate.valid, candidate.inside, by
      change (Line.Proj.affine reading.value).Equivalent
        (Line.Matrix.act occurrence.snapshot.frame.matrix (Line.Proj.affine (Reply.ofRealization realization).tail))
      rewrite [Reply.ofRealization_tail]
      exact represented⟩
  exact
    { candidate := by
        change Reply.Candidate occurrence.reply _
        exact occurrence.replyEq.symm ▸ affineCandidate
      numerical := by
        change Reply.Numerical occurrence.reply
        exact occurrence.replyEq.symm ▸ Reply.ofSnapshot_numerical occurrence.snapshot
      previousWord := occurrence.previousWord
      wordPrefix := occurrence.wordPrefix
      length := occurrence.length
      accurate := occurrence.accurate }

/-- Cache the realizations of the exact ordered occurrence list, using one shared already computed final image. -/
private def realizeOccurrences {initial : Machine.Snapshot} {origin : State initial} (recording : Recording origin)
    (survivor : Machine.History.Survivor recording.current.history) {process : Process} {state : process.State}
    (reading : Reading survivor process state) :
    (occurrences : List (Occurrence origin)) → (∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences) →
      List ((entry : Basic.Exchange Question Reply) × Realization entry reading.value)
  | [], _ => []
  | occurrence :: rest, retained =>
      ⟨occurrence.exchange, realizeOccurrence recording survivor reading occurrence
        (retained occurrence (List.Mem.head rest))⟩ ::
          realizeOccurrences recording survivor reading rest
            (fun entry member => retained entry (List.Mem.tail occurrence member))

/-- Cached realization production preserves every original exchange and repeated occurrence in order. -/
private theorem realizeOccurrences_projection {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (survivor : Machine.History.Survivor recording.current.history)
    {process : Process} {state : process.State} (reading : Reading survivor process state) :
    (occurrences : List (Occurrence origin)) →
      (retained : ∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences) →
      (realizeOccurrences recording survivor reading occurrences retained).map Sigma.fst =
        occurrences.map Occurrence.exchange
  | [], _ => rfl
  | occurrence :: rest, retained =>
      congrArg (List.cons occurrence.exchange)
        (realizeOccurrences_projection recording survivor reading rest
          (fun entry member => retained entry (List.Mem.tail occurrence member)))

/-- Describe an actual old occurrence using its same cached numerical reply and computed rational candidate. -/
private def codeOfOccurrence {initial : Machine.Snapshot} {origin : State initial} (recording : Recording origin)
    (survivor : Machine.History.Survivor recording.current.history) {process : Process} {state : process.State}
    (reading : Reading survivor process state) (occurrence : Occurrence origin)
    (member : occurrence ∈ recording.occurrences) : {code : Continuation.Code // Continuation.Valid code} :=
  let realization := realizeOccurrence recording survivor reading occurrence member
  Continuation.Code.ofCandidate reading.value occurrence.reply realization.candidate realization.numerical

/-- The occurrence description retains its exact original reply and the same shared rational reading. -/
private theorem codeOfOccurrence_specification {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) (survivor : Machine.History.Survivor recording.current.history)
    {process : Process} {state : process.State} (reading : Reading survivor process state)
    (occurrence : Occurrence origin) (member : occurrence ∈ recording.occurrences) :
    (codeOfOccurrence recording survivor reading occurrence member).val.point = reading.value ∧
      (codeOfOccurrence recording survivor reading occurrence member).val.reply = occurrence.reply := ⟨rfl, rfl⟩

/-- Cache finite rational codes for exactly the original new-request occurrences, leaving recalls in the full trace. -/
private def spineCodes {initial : Machine.Snapshot} {origin : State initial} (recording : Recording origin)
    (survivor : Machine.History.Survivor recording.current.history) {process : Process} {state : process.State}
    (reading : Reading survivor process state) :
    (occurrences : List (Occurrence origin)) → (∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences) →
      List Continuation.Step
  | [], _ => []
  | occurrence :: remaining, retained =>
      let certified := codeOfOccurrence recording survivor reading occurrence
        (retained occurrence (List.Mem.head remaining))
      ⟨occurrence.question.request, certified.val⟩ :: spineCodes recording survivor reading remaining
        (fun entry member => retained entry (List.Mem.tail occurrence member))

/-- Realizing the actual chronological spine preserves every preceding code, prefix and numerical payment. -/
private theorem spineCodes_chain {initial : Machine.Snapshot} {origin : State initial} (recording : Recording origin)
    (survivor : Machine.History.Survivor recording.current.history) {process : Process} {state : process.State}
    (reading : Reading survivor process state)
    {path : List Request} {reply : Reply} {occurrences : List (Occurrence origin)}
    {endPath : List Request} {endReply : Reply} (spine : Spine origin path reply occurrences endPath endReply)
    (retained : ∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences)
    (earlier : Continuation.Code) (pointEq : earlier.point = reading.value) (replyEq : earlier.reply = reply) :
    Continuation.Chain earlier (spineCodes recording survivor reading occurrences retained) := by
  induction spine generalizing earlier with
  | nil path reply => exact .nil earlier
  | cons occurrence path reply questionEq wordEq tail induction =>
      let member := retained occurrence (List.Mem.head _)
      let certified := codeOfOccurrence recording survivor reading occurrence member
      have specification := codeOfOccurrence_specification recording survivor reading occurrence member
      apply Continuation.Chain.cons
      · exact
          { nextValid := certified.property
            pointEq := specification.1.trans pointEq.symm
            wordPrefix := by rewrite [specification.2, replyEq, ← wordEq]; exact occurrence.wordPrefix
            length := by
              intro count same
              rewrite [specification.2, replyEq, ← wordEq]
              exact occurrence.length count same
            accurate := by
              intro target positive same
              rewrite [specification.2]
              exact occurrence.accurate target positive same }
      · exact induction (fun entry member => retained entry (List.Mem.tail occurrence member))
          certified.val specification.1 specification.2

/-- The finite rational spine retains exactly the original new-request questions and complete numerical replies. -/
private theorem spineCodes_trace {initial : Machine.Snapshot} {origin : State initial} (recording : Recording origin)
    (survivor : Machine.History.Survivor recording.current.history) {process : Process} {state : process.State}
    (reading : Reading survivor process state)
    {path : List Request} {reply : Reply} {occurrences : List (Occurrence origin)}
    {endPath : List Request} {endReply : Reply} (spine : Spine origin path reply occurrences endPath endReply)
    (retained : ∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences) :
    Continuation.History.traceFrom path (spineCodes recording survivor reading occurrences retained) =
      occurrences.map Occurrence.exchange := by
  induction spine with
  | nil path reply => rfl
  | cons occurrence path reply questionEq wordEq tail induction =>
      have specification := codeOfOccurrence_specification recording survivor reading occurrence
        (retained occurrence (List.Mem.head _))
      have actualQuestion : (Path.Question.mk path occurrence.question.request) = occurrence.question :=
        congrArg (fun previous => Path.Question.mk previous occurrence.question.request) questionEq.symm
      have actualPath : path ++ [occurrence.question.request] = occurrence.question.path :=
        congrArg (fun previous => previous ++ [occurrence.question.request]) questionEq.symm
      refine congrArg₂ List.cons ?_ ?_
      · change (⟨⟨path, occurrence.question.request⟩, _⟩ : Basic.Exchange Question Reply) = occurrence.exchange
        rewrite [specification.2, actualQuestion]
        rfl
      · exact actualPath.symm ▸
          induction (fun entry member => retained entry (List.Mem.tail occurrence member))

/-- Admit every actual mixed recording using one final rational witness and its original Gaussian-source certificate.

All earlier tails consume their retained inverse-chart caches and the same
final image. Each cached original ball, complete word, prefix payment and
strict accuracy certificate is retained, including empty and repeated traces.
-/
def admission {initial : Machine.Snapshot} {origin : State initial} (recording : Recording origin)
    {process : Process} {state : process.State}
    (initialCursor : Machine.Semantics.Basic.ExactCursor process state initial.machine) :
    Admitted recording.trace := by
  let survivor := recording.current.history.survive
  let reading := survivor.read initialCursor
  let realizations := realizeOccurrences recording survivor reading recording.occurrences (fun _ member => member)
  let currentRealization := recording.current.history.realize recording.current.history.current
    recording.current.history.currentMember survivor.tail survivor.possible survivor.image survivor.imageEq
  let candidate := Reply.ofRealization currentRealization
  let currentCandidate : Reply.Candidate (Reply.ofSnapshot recording.current.history.current)
      (Line.Proj.affine reading.value) :=
    ⟨candidate.tail, candidate.valid, candidate.inside, by
      change (Line.Proj.affine reading.value).Equivalent
        (recording.current.history.current.frame.image (Reply.ofRealization currentRealization).tail)
      rewrite [Reply.ofRealization_tail]
      exact Line.Proj.Equivalent.symm (reading.snapshot_represented currentRealization)⟩
  let originalRealization := recording.current.history.realize origin.history.current recording.originRetained
    survivor.tail survivor.possible survivor.image survivor.imageEq
  let originalCandidate := Reply.ofRealization originalRealization
  let affineOriginal : Reply.Candidate (Reply.ofSnapshot origin.history.current) (Line.Proj.affine reading.value) :=
    ⟨originalCandidate.tail, originalCandidate.valid, originalCandidate.inside, by
      change (Line.Proj.affine reading.value).Equivalent
        (origin.history.current.frame.image (Reply.ofRealization originalRealization).tail)
      rewrite [Reply.ofRealization_tail]
      exact Line.Proj.Equivalent.symm (reading.snapshot_represented originalRealization)⟩
  let initialCandidate : Reply.Candidate origin.reply (Line.Proj.affine reading.value) :=
    origin.replyEq.symm ▸ affineOriginal
  let initialCode := Continuation.Code.ofCandidate reading.value origin.reply initialCandidate origin.numerical
  let steps := spineCodes recording survivor reading recording.spine recording.spineIncluded
  let history : Continuation.History := ⟨initialCode.val, steps⟩
  have savedTrace : history.trace = recording.spine.map Occurrence.exchange :=
    spineCodes_trace recording survivor reading recording.spineEq recording.spineIncluded
  exact
    { point := reading.value
      realizations := realizations
      traceEq := (realizeOccurrences_projection recording survivor reading recording.occurrences
        (fun _ member => member)).trans recording.traceEq.symm
      current := recording.current.reply
      currentCandidate := recording.current.replyEq.symm ▸ currentCandidate
      currentNumerical := recording.current.numerical
      history := history
      historyValid := ⟨initialCode.property,
        spineCodes_chain recording survivor reading recording.spineEq recording.spineIncluded initialCode.val rfl rfl⟩
      historyPoint := rfl
      covered := by
        intro entry member
        have mapped : entry ∈ recording.occurrences.map Occurrence.exchange := recording.traceEq ▸ member
        rcases Data.List.Map.mem_map.mp mapped with ⟨occurrence, included, rfl⟩
        exact savedTrace.symm ▸ Data.List.Map.mem_map.mpr
          ⟨occurrence, recording.covered occurrence included, rfl⟩
      consistent := by
        intro left leftMember right rightMember same
        exact (recording.answers left leftMember).symm.trans
          ((congrArg (answer origin) same).trans (recording.answers right rightMember)) }

/-- The admission builder retains its actual computed final affine reading and exact current numerical reply. -/
private theorem admit_specification {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) {process : Process} {state : process.State}
    (initialCursor : Machine.Semantics.Basic.ExactCursor process state initial.machine) :
    (recording.admission initialCursor).point = (recording.current.history.survive.read initialCursor).value ∧
      (recording.admission initialCursor).current = recording.current.reply := ⟨rfl, rfl⟩

/-- The mixed admission's explicit rational reading was possible at the same original Gaussian source state. -/
theorem admit_originalPossible {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) {process : Process} {state : process.State}
    (initialCursor : Machine.Semantics.Basic.ExactCursor process state initial.machine) :
    process.Possible state (recording.admission initialCursor).point :=
  (admit_specification recording initialCursor).1.symm ▸
    (recording.current.history.survive.read initialCursor).originalPossible

/-- Mixed admission retains the exact final cached numerical reply for later continuation. -/
theorem admit_current {initial : Machine.Snapshot} {origin : State initial}
    (recording : Recording origin) {process : Process} {state : process.State}
    (initialCursor : Machine.Semantics.Basic.ExactCursor process state initial.machine) :
    (recording.admission initialCursor).current = recording.current.reply :=
  (admit_specification recording initialCursor).2

end Recording

end Purelib.Approximation.Gaussian.Observation.Cursor.Source

end
