module

public import Purelib.Approximation.Gaussian.Process.Observation
public import Purelib.Computation.Query.Basic
public import Purelib.Computation.Query.Path
public import Purelib.Data.List.Append
public import Purelib.Data.List.Map
public import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

/-!
# Numerical enclosure questions on an actual finite refinement path

A question retains the full finite path from an original process state and
one positive squared-error request. Its numerical reply is the actual ball
at the resulting state. Identical questions denote identical transitions;
counterfactual paths impose no conditions on an executed transcript.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation

open Purelib.Approximation
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Computation.Query

set_option genInjectivity false in
/-- A positive rational squared-error request with its exact positivity certificate. -/
structure Request where
  /-- The displayed rational squared-error target. -/ targetSq : Fraction.Rational
  /-- The target permits an arbitrary-accuracy process request. -/ positive : 0 < targetSq

namespace Request

/-- Construct a request from the supplied target and its retained positivity evidence. -/
@[expose] def ofPositive (targetSq : Fraction.Rational) (positive : 0 < targetSq) : Request :=
  ⟨targetSq, positive⟩

/-- Compare requests by their numerical targets; positivity proofs are not numerical observations. -/
instance : DecidableEq Request := fun left right =>
  if equal : left.targetSq = right.targetSq then
    .isTrue (by cases left; cases right; cases equal; rfl)
  else .isFalse (fun same => equal (congrArg Request.targetSq same))

set_option genInjectivity false in
/-- Exact target checking returns a certified request or the violated positivity condition. -/
inductive Check (targetSq : Fraction.Rational) where
  /-- The same displayed target has a positive request certificate. -/ | valid
      (request : Request) (targetEq : request.targetSq = targetSq)
  /-- The displayed target fails the required strict positivity condition. -/ | invalid
      (notPositive : ¬ 0 < targetSq)

/-- Check a rational target by exact comparison and retain evidence of either outcome. -/
@[expose] def check (targetSq : Fraction.Rational) : Check targetSq :=
  if positive : 0 < targetSq then .valid (ofPositive targetSq positive) rfl
  else .invalid positive

end Request

/-- One numerical request after an exact finite path from the retained initial state. -/
abbrev Question := Path.Question Request

namespace Question

/-- Construct the first question at a retained initial state. -/
@[expose] def initial (request : Request) : Question :=
  Path.Question.initial request

/-- Read the complete request path after this question has been answered. -/
@[expose] def path (question : Question) : List Request :=
  Path.Question.path question

/-- Construct a question extending the exact earlier question's request path. -/
@[expose] def next (question : Question) (request : Request) : Question :=
  Path.Question.next question request

end Question

set_option genInjectivity false in
/-- A certified common rational reading of one exact numerical enclosure trace.

Every occurrence retains containment and strict target accuracy. Consistency
compares complete replies at repeated identical path questions. A source
producer computes this certificate from its final actual process witness;
admission is not an assumed existential rational completion.
-/
structure Admitted (trace : Computation.Query.Basic.Trace Question Enclosure.Ball) where
  /-- The cached Gaussian rational reading satisfying every recorded occurrence. -/ point :
    Gaussian.Basic.Canonical
  /-- The same cached reading lies in each actual recorded ball. -/ inside :
    ∀ entry ∈ trace, entry.reply.Contains point
  /-- Each actual recorded reply pays its original positive squared-error request. -/ accurate :
    ∀ entry ∈ trace, entry.reply.radiusSq < entry.query.request.targetSq
  /-- Repeated identical questions retain exactly the same numerical reply. -/ consistent :
    ∀ left ∈ trace, ∀ right ∈ trace, left.query = right.query → left.reply = right.reply

namespace Source

open Purelib.Data.List

/-- Execute a finite request path on the same original process and retained initial state. -/
@[expose] def stateAfter (process : Gaussian.Process) :
    process.State → List Request → process.State
  | state, [] => state
  | state, request :: rest =>
      stateAfter process (process.refine state request.targetSq request.positive) rest

/-- Finite path execution preserves every earlier admitted reading along that path. -/
theorem stateAfter_persists (process : Gaussian.Process) (initial : process.State)
    (requests : List Request) {value : Gaussian.Basic.Canonical}
    (possible : process.Possible (stateAfter process initial requests) value) :
    process.Possible initial value := by
  induction requests generalizing initial with
  | nil => exact possible
  | cons request rest induction =>
      exact process.refine_persists initial request.targetSq request.positive
        (induction _ possible)

/-- The query denotes one actual refinement of the state reached by its preceding path. -/
@[expose] def answer (process : Gaussian.Process) (initial : process.State)
    (question : Question) : Enclosure.Ball :=
  process.ball (process.refine (stateAfter process initial question.previous)
    question.request.targetSq question.request.positive)

/-- The source's actual numerical reply pays the question's strict squared-error target. -/
theorem answer_accurate (process : Gaussian.Process) (initial : process.State)
    (question : Question) : (answer process initial question).radiusSq < question.request.targetSq :=
  process.accurate _ _ _

/-- Execute an appended request path by continuing from the actual preceding state. -/
theorem stateAfter_append (process : Gaussian.Process) (initial : process.State)
    (before after : List Request) :
    stateAfter process initial (before ++ after) =
      stateAfter process (stateAfter process initial before) after := by
  induction before generalizing initial with
  | nil => rfl
  | cons request rest induction => exact induction _

/-- The query reply is exactly the ball reached by its complete request path. -/
theorem answer_eq_path_ball (process : Gaussian.Process) (initial : process.State)
    (question : Question) : answer process initial question =
      process.ball (stateAfter process initial question.path) := by
  unfold Question.path Path.Question.path
  rewrite [stateAfter_append]
  rfl

set_option genInjectivity false in
/-- Retain the actual current process state and its exact chronological request path.

The cached state belongs to the original process and initial state. Its
specification identifies the finite path interpreter, while its generic
observation history retains the actual refinement certificates.
-/
structure Snapshot (process : Gaussian.Process) (initial : process.State) where
  /-- The actual cached process state after the retained requests. -/ state : process.State
  /-- The exact preceding requests, in their execution order. -/ path : List Request
  /-- The actual number of fresh source refinements, cached independently of the path spine. -/ requestCount : Nat
  /-- The cached refinement count identifies this same original finite request path. -/ requestCountEq :
    requestCount = path.length
  /-- The actual current ball, possible witness and generic observation, each prepared once. -/ observation :
    Process.Observation process state
  /-- The cached state is the state denoted by this original request path. -/ stateEq :
    state = stateAfter process initial path
  /-- The actual process refinements extend the original generic observation history. -/ history :
    Approximation.Observation.History (process.observation initial) (process.observation state)

namespace Snapshot

/-- Start a snapshot at the exact original state without making a request. -/
@[expose] def initial (process : Gaussian.Process) (state : process.State) : Snapshot process state :=
  ⟨state, [], 0, rfl, Process.Observation.build process state, rfl, .start⟩

/-- Form the next numerical question from the exact cached request path. -/
@[expose] def question {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) (request : Request) : Question :=
  ⟨snapshot.path, request⟩

/-- Advance the actual cached state once and retain its original refinement history.

The source refinement consumes the existing state directly. The finite path
interpreter is used only in the specification proof; it is not rerun to
compute the new state.
-/
@[expose] def request {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) (request : Request) : Snapshot process initial := by
  let state := process.refine snapshot.state request.targetSq request.positive
  let path := snapshot.path ++ [request]
  let observation := Process.Observation.build process state
  have stateEq : state = stateAfter process initial path := by
    unfold path
    rewrite [stateAfter_append]
    change state = process.refine (stateAfter process initial snapshot.path)
      request.targetSq request.positive
    rewrite [← snapshot.stateEq]
    rfl
  exact
    { state := state
      path := path
      requestCount := snapshot.requestCount + 1
      requestCountEq := (congrArg (fun count => count + 1) snapshot.requestCountEq).trans
        (Append.length_append snapshot.path [request]).symm
      observation := observation
      stateEq := stateEq
      history := snapshot.observation.extendHistory observation request.targetSq request.positive rfl snapshot.history }

/-- A snapshot request appends exactly its supplied request to the cached path. -/
theorem request_path {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) (target : Request) :
    (snapshot.request target).path = snapshot.path ++ [target] := rfl

/-- A snapshot request uses the original cached state in the actual process transition. -/
theorem request_state {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) (target : Request) :
    (snapshot.request target).state = process.refine snapshot.state target.targetSq target.positive := rfl

/-- Read the exact number of original refinement callbacks from the retained request counter. -/
@[expose] def refinementCalls {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) : Nat := snapshot.requestCount

/-- Read the original ball callbacks, including the one explicit initial observation. -/
@[expose] def ballCalls {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) : Nat := snapshot.requestCount + 1

/-- Read the original witness callbacks, including the one explicit initial observation. -/
@[expose] def witnessCalls {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) : Nat := snapshot.requestCount + 1

/-- Count displayed source-interface callbacks separately from numerical machine transitions.

Initialization reads one ball and one witness. Each fresh request refines once
and reads its new ball and witness once; history extension and admission use
those same caches. This count covers interface calls, not arbitrary work hidden
inside a supplied process implementation.
-/
@[expose] def sourceCalls {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) : Nat :=
  snapshot.refinementCalls + snapshot.ballCalls + snapshot.witnessCalls

/-- The original setup and fresh refinements account for every displayed source-interface call. -/
theorem sourceCalls_eq_requests {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) : snapshot.sourceCalls = 2 + 3 * snapshot.requestCount := by
  change (snapshot.requestCount + (snapshot.requestCount + 1)) + (snapshot.requestCount + 1) = _
  omega0

/-- Each actual source transition consumes exactly three further displayed interface callbacks. -/
theorem request_sourceCalls {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) (target : Request) :
    (snapshot.request target).sourceCalls = snapshot.sourceCalls + 3 := by
  change ((snapshot.requestCount + 1) + (snapshot.requestCount + 1 + 1)) +
      (snapshot.requestCount + 1 + 1) =
    ((snapshot.requestCount + (snapshot.requestCount + 1)) + (snapshot.requestCount + 1)) + 3
  omega0

/-- The explicit original setup performs one ball callback and one witness callback. -/
theorem initial_sourceCalls (process : Gaussian.Process) (state : process.State) :
    (Snapshot.initial process state).sourceCalls = 2 := rfl

end Snapshot

set_option genInjectivity false in
/-- One actual source transition and its cached numerical reply.

Both original process states, the exact path question and the original ball
are retained. Their equalities identify the actual transition and readback;
the generic history preserves every preceding refinement certificate.
-/
structure Occurrence (process : Gaussian.Process) (initial : process.State) where
  /-- The complete numerical question for this actual transition. -/ question : Question
  /-- The original process state consumed by the transition. -/ before : process.State
  /-- The actual process state returned by the transition. -/ after : process.State
  /-- The preceding path denotes the same original consumed state. -/ beforeEq :
    before = stateAfter process initial question.previous
  /-- The returned state is the actual refinement of that consumed state. -/ afterEq :
    after = process.refine before question.request.targetSq question.request.positive
  /-- The cached numerical ball read from the returned state. -/ reply : Enclosure.Ball
  /-- The cached reply is the original returned state's actual ball. -/ replyEq : reply = process.ball after
  /-- The actual transition retains the complete generic observation history. -/ history :
    Approximation.Observation.History (process.observation initial) (process.observation after)

namespace Occurrence

/-- Record one supplied snapshot transition and read its numerical reply once. -/
@[expose] def ofRequest {process : Gaussian.Process} {initial : process.State}
    (snapshot : Snapshot process initial) (target : Request)
    (next : Snapshot process initial) (nextEq : next = snapshot.request target) :
    Occurrence process initial :=
  { question := snapshot.question target
    before := snapshot.state
    after := next.state
    beforeEq := snapshot.stateEq
    afterEq := (congrArg Snapshot.state nextEq).trans (snapshot.request_state target)
    reply := next.observation.ball
    replyEq := next.observation.ballEq
    history := next.history }

/-- Project the exact cached question and numerical reply into the generic exchange carrier. -/
@[expose] def exchange {process : Gaussian.Process} {initial : process.State}
    (occurrence : Occurrence process initial) : Computation.Query.Basic.Exchange Question Enclosure.Ball :=
  ⟨occurrence.question, occurrence.reply⟩

/-- The pure path question denotes this same actual cached numerical reply. -/
theorem answerEq {process : Gaussian.Process} {initial : process.State}
    (occurrence : Occurrence process initial) : answer process initial occurrence.question = occurrence.reply := by
  unfold answer
  rewrite [← occurrence.beforeEq, ← occurrence.afterEq]
  exact occurrence.replyEq.symm

/-- The actual returned state is the state denoted by the complete original question path. -/
theorem pathStateEq {process : Gaussian.Process} {initial : process.State}
    (occurrence : Occurrence process initial) :
    occurrence.after = stateAfter process initial occurrence.question.path := by
  unfold Question.path Path.Question.path
  rewrite [stateAfter_append]
  change occurrence.after = process.refine
    (stateAfter process initial occurrence.question.previous)
    occurrence.question.request.targetSq occurrence.question.request.positive
  rewrite [← occurrence.beforeEq]
  exact occurrence.afterEq

/-- The actual recorded ball pays its original positive target. -/
theorem accurate {process : Gaussian.Process} {initial : process.State}
    (occurrence : Occurrence process initial) :
    occurrence.reply.radiusSq < occurrence.question.request.targetSq := by
  rewrite [occurrence.replyEq, occurrence.afterEq]
  exact process.accurate _ _ _

end Occurrence

set_option genInjectivity false in
/-- A chronological source recording retaining the original states and exact ordered numerical trace.

Every recorded transition lies on the actual executed refinement spine.
The cached trace is the exact numerical projection of the retained
occurrences, including repetitions; no counterfactual path is added.
-/
structure Recording (process : Gaussian.Process) (initial : process.State) where
  /-- The actual cached current state, request path and original observation history. -/ current :
    Snapshot process initial
  /-- The original state transitions in their recorded occurrence order. -/ occurrences :
    List (Occurrence process initial)
  /-- The cached exact ordered numerical trace, including repeated questions. -/ trace :
    Computation.Query.Basic.Trace Question Enclosure.Ball
  /-- The numerical trace projects these same retained occurrences exactly. -/ traceEq :
    trace = occurrences.map Occurrence.exchange
  /-- Every recorded transition lies on the same actual executed request path. -/ onSpine :
    ∀ occurrence ∈ occurrences, occurrence.question.path.IsPrefix current.path

namespace Recording

set_option genInjectivity false in
/-- Retain the actual new snapshot, cached occurrence and complete recording of one source request.

The request is executed once. All projections consume the same original
parents and computed caches; the resulting recording appends that exact
occurrence and exchange to its preceding histories.
-/
structure RequestResult {process : Gaussian.Process} {initial : process.State}
    (previous : Recording process initial) (target : Request) where
  /-- The actual new snapshot computed from the cached preceding state. -/ snapshot : Snapshot process initial
  /-- The snapshot is this exact original request transition. -/ snapshotEq : snapshot = previous.current.request target
  /-- The actual cached transition and numerical reply. -/ occurrence : Occurrence process initial
  /-- The occurrence consumes the same original parent and computed snapshot. -/ occurrenceEq :
    occurrence = Occurrence.ofRequest previous.current target snapshot snapshotEq
  /-- The actual resulting complete source recording. -/ next : Recording process initial
  /-- The resulting recording consumes this same new snapshot. -/ currentEq : next.current = snapshot
  /-- The resulting recording retains every earlier occurrence and this actual new one. -/ occurrencesEq :
    next.occurrences = previous.occurrences ++ [occurrence]
  /-- The resulting recording appends the exact cached numerical exchange. -/ traceEq :
    next.trace = previous.trace ++ [occurrence.exchange]

/-- Start the chronological source recording with its original state and an empty trace. -/
@[expose] def initial (process : Gaussian.Process) (state : process.State) : Recording process state :=
  { current := Snapshot.initial process state
    occurrences := []
    trace := []
    traceEq := rfl
    onSpine := fun _ member => nomatch member }

/-- Compute one source request and retain its actual new state, cached reply and complete recording. -/
def prepareRequest {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) (target : Request) : RequestResult recording target := by
  let snapshot := recording.current.request target
  let occurrence := Occurrence.ofRequest recording.current target snapshot rfl
  let next : Recording process initial :=
    { current := snapshot
      occurrences := recording.occurrences ++ [occurrence]
      trace := recording.trace ++ [occurrence.exchange]
      traceEq := by
        rewrite [Map.map_append, ← recording.traceEq]
        rfl
      onSpine := by
        intro previous member
        rcases Membership.mem_append.mp member with earlier | last
        · rcases recording.onSpine previous earlier with ⟨suffix, pathEq⟩
          refine ⟨suffix ++ [target], ?_⟩
          calc
            previous.question.path ++ (suffix ++ [target]) =
                (previous.question.path ++ suffix) ++ [target] :=
              (Append.append_assoc _ _ _).symm
            _ = recording.current.path ++ [target] := congrArg (fun path => path ++ [target]) pathEq
            _ = snapshot.path := (recording.current.request_path target).symm
        · have same := Membership.mem_singleton.mp last
          cases same
          exact ⟨[], Append.append_nil occurrence.question.path⟩ }
  exact ⟨snapshot, rfl, occurrence, rfl, next, rfl, rfl, rfl⟩

/-- Advance the cached source once and return the same prepared request's complete recording. -/
def request {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) (target : Request) : Recording process initial :=
  (recording.prepareRequest target).next

namespace RequestResult

/-- The actual cached occurrence records the question of the exact preceding snapshot. -/
theorem questionEq {process : Gaussian.Process} {initial : process.State}
    {previous : Recording process initial} {target : Request} (result : RequestResult previous target) :
    result.occurrence.question = previous.current.question target :=
  congrArg Occurrence.question result.occurrenceEq

/-- The actual resulting snapshot extends the exact earlier request path. -/
theorem pathEq {process : Gaussian.Process} {initial : process.State}
    {previous : Recording process initial} {target : Request} (result : RequestResult previous target) :
    result.next.current.path = previous.current.path ++ [target] :=
  (congrArg Snapshot.path result.currentEq).trans
    ((congrArg Snapshot.path result.snapshotEq).trans (previous.current.request_path target))

/-- The cached reply equals the original path adapter's answer at that same retained question. -/
theorem replyEq {process : Gaussian.Process} {initial : process.State}
    {previous : Recording process initial} {target : Request} (result : RequestResult previous target) :
    result.occurrence.reply = answer process initial (previous.current.question target) :=
  result.occurrence.answerEq.symm.trans (congrArg (answer process initial) result.questionEq)

end RequestResult

/-- Repeat an actual cached occurrence without refining or rereading its original source state. -/
@[expose] def recall {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) (occurrence : Occurrence process initial)
    (member : occurrence ∈ recording.occurrences) : Recording process initial :=
  { current := recording.current
    occurrences := recording.occurrences ++ [occurrence]
    trace := recording.trace ++ [occurrence.exchange]
    traceEq := by
      rewrite [Map.map_append, ← recording.traceEq]
      rfl
    onSpine := by
      intro previous present
      rcases Membership.mem_append.mp present with earlier | last
      · exact recording.onSpine previous earlier
      · exact (Membership.mem_singleton.mp last).symm ▸ recording.onSpine occurrence member }

/-- Recalling an original occurrence leaves the exact current source snapshot unchanged. -/
theorem recall_current {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) (occurrence : Occurrence process initial)
    (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).current = recording.current := rfl

/-- Recalling an original occurrence appends that same cached exchange to the exact trace. -/
theorem recall_trace {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) (occurrence : Occurrence process initial)
    (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).trace = recording.trace ++ [occurrence.exchange] := rfl

/-- Every numerical trace occurrence is the reply of the same original pure path adapter. -/
theorem answers {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) :
    Computation.Query.Basic.Answers (answer process initial) recording.trace := by
  intro entry member
  have mapped : entry ∈ recording.occurrences.map Occurrence.exchange := recording.traceEq ▸ member
  rcases Map.mem_map.mp mapped with ⟨occurrence, _present, rfl⟩
  exact occurrence.answerEq

/-- The actual final process witness satisfies every original recorded process state on the executed spine. -/
theorem witness_possible {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) (occurrence : Occurrence process initial)
    (member : occurrence ∈ recording.occurrences) :
    process.Possible occurrence.after recording.current.observation.witness.val := by
  let point := recording.current.observation.witness.val
  have finalPossible : process.Possible (stateAfter process initial recording.current.path) point :=
    recording.current.stateEq ▸ recording.current.observation.witness.property
  rcases recording.onSpine occurrence member with ⟨suffix, pathEq⟩
  have combined : process.Possible
      (stateAfter process initial (occurrence.question.path ++ suffix)) point :=
    (congrArg (stateAfter process initial) pathEq).symm ▸ finalPossible
  have afterSuffix : process.Possible
      (stateAfter process (stateAfter process initial occurrence.question.path) suffix) point :=
    stateAfter_append process initial occurrence.question.path suffix ▸ combined
  have earlier := stateAfter_persists process
    (stateAfter process initial occurrence.question.path) suffix afterSuffix
  exact occurrence.pathStateEq.symm ▸ earlier

/-- Construct admission from the final actual source witness and the complete recorded finite spine.

This executable producer caches one Gaussian rational reading and proves
its containment at every recorded occurrence. Empty traces and repeated
questions use the same construction; no rational realizer is assumed.
-/
def admission {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) : Admitted recording.trace := by
  let point := recording.current.observation.witness.val
  exact
    { point := point
      inside := by
        intro entry member
        have mapped : entry ∈ recording.occurrences.map Occurrence.exchange := recording.traceEq ▸ member
        rcases Map.mem_map.mp mapped with ⟨occurrence, present, rfl⟩
        have possible := recording.witness_possible occurrence present
        change occurrence.reply.Contains point
        rewrite [occurrence.replyEq]
        exact process.possible_inside possible
      accurate := by
        intro entry member
        have mapped : entry ∈ recording.occurrences.map Occurrence.exchange := recording.traceEq ▸ member
        rcases Map.mem_map.mp mapped with ⟨occurrence, _present, rfl⟩
        exact occurrence.accurate
      consistent := by
        intro left leftMember right rightMember same
        exact (recording.answers left leftMember).symm.trans
          ((congrArg (answer process initial) same).trans (recording.answers right rightMember)) }

/-- Read the actual recording's displayed source-interface callback count from its cached current state. -/
@[expose] def sourceCalls {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) : Nat := recording.current.sourceCalls

/-- One actual fresh source request adds its refinement, ball read and witness read to the same recording. -/
theorem request_sourceCalls {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) (target : Request) :
    (recording.request target).sourceCalls = recording.sourceCalls + 3 := by
  let result := recording.prepareRequest target
  have current := congrArg Snapshot.sourceCalls result.currentEq
  have snapshot := congrArg Snapshot.sourceCalls result.snapshotEq
  exact current.trans (snapshot.trans (recording.current.request_sourceCalls target))

/-- An actual retained recall invokes no source refinement, ball or witness callback. -/
theorem recall_sourceCalls {process : Gaussian.Process} {initial : process.State}
    (recording : Recording process initial) (occurrence : Occurrence process initial)
    (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).sourceCalls = recording.sourceCalls :=
  congrArg Snapshot.sourceCalls (recording.recall_current occurrence member)

/-- Execute a finite request list by advancing the same cached recording at each step. -/
def requestMany {process : Gaussian.Process} {initial : process.State} :
    Recording process initial → List Request → Recording process initial
  | recording, [] => recording
  | recording, target :: rest => requestMany (recording.request target) rest

/-- Produce one chronological recording from an original state and finite numerical request list. -/
def ofRequests (process : Gaussian.Process) (initial : process.State) (requests : List Request) :
    Recording process initial := requestMany (Recording.initial process initial) requests

/-- Produce and admit one actual recording without repeating its source requests.

The returned first component owns the cached states and trace; the second
is indexed by that exact trace and retains its computed rational survivor.
Clients read both components directly instead of rerunning the producer to
recover the admitted trace.
-/
def admitRequests (process : Gaussian.Process) (initial : process.State) (requests : List Request) :
    (recording : Recording process initial) × Admitted recording.trace :=
  let recording := ofRequests process initial requests
  ⟨recording, recording.admission⟩

end Recording

end Source

end Purelib.Approximation.Gaussian.Observation

end
