module

public import Purelib.Approximation.Gaussian.Observation.Prefix.Transcript
public import Purelib.Approximation.Gaussian.Observation.Prefix.Continuation
import Purelib.Computation.Query.Path
import Purelib.Approximation.Gaussian.Observation.Cursor.Request
public import Purelib.Geometry.CCL.Prefix.Path
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Neighborhood
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership

/-!
# Actual mixed requests on canonical proper prefix enclosures

Additional bits use the original homographic proper-box path builder.
Accuracy requests choose a strict inner neighbourhood while retaining the
same exact word, parser and inverse chart. One final sample then satisfies
every original reply and prefix throughout the actual finite request spine.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Prefix

open Purelib
open Purelib.Data
open Purelib.Data.CCL
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Computation.Query

namespace Reply

/-- Display the same retained canonical word and chart caches with the actual box's enclosing ambient ball. -/
@[expose] def ofEnclosure (enclosure : Encoding.Prefix.Enclosure) : Reply :=
  ⟨enclosure.word, enclosure.state, enclosure.inverseMatrix, enclosure.box.enclosure, false⟩

/-- Every point in the original proper box realizes its same cached canonical numerical reply. -/
def candidateOfEnclosure (enclosure : Encoding.Prefix.Enclosure) (point : Gaussian.Basic.Canonical)
    (inside : enclosure.box.Contains point) : Candidate (ofEnclosure enclosure) point :=
  ⟨enclosure.tail point, enclosure.stateSpec, enclosure.determinant, enclosure.inverseSpec, rfl,
    enclosure.tail_represents inside, enclosure.box.inside_enclosure inside,
    fun impossible => by nomatch impossible⟩

end Reply

namespace Source

set_option genInjectivity false in
/-- One original canonical checkpoint retains its exact prefix enclosure and already computed numerical reply. -/
structure Snapshot where
  /-- The original proper enclosure with exact word and cached affine parser charts. -/ enclosure :
    Encoding.Prefix.Enclosure
  /-- The same original numerical reply, computed once. -/ reply : Reply
  /-- The reply belongs to that exact original enclosure. -/ replyEq : reply = Reply.ofEnclosure enclosure

namespace Snapshot

/-- Start a cached canonical source at an existing proper prefix enclosure without rebuilding its parser or inverse. -/
@[expose] def ofEnclosure (enclosure : Encoding.Prefix.Enclosure) : Snapshot :=
  ⟨enclosure, Reply.ofEnclosure enclosure, rfl⟩

/-- Compute the original direct inner box for one positive squared-accuracy request. -/
@[expose] def accuracyBox (earlier : Snapshot) (target : Fraction.Rational) (positive : 0 < target) :
    Rational.Box :=
  Rational.Box.Neighborhood.innerBox earlier.enclosure.box earlier.enclosure.box.midpoint
    (earlier.enclosure.box.midpoint_strictContains earlier.enclosure.proper) (target / 4)
    (Fraction.Order.Field.div_pos_direct positive (by decide))

end Snapshot

set_option genInjectivity false in
/-- An actual source request retains its geometric construction and exact returned checkpoint.

Bit requests keep the complete original path, including every selected sample
and polynomial evaluation. Accuracy requests keep the original returned box
and its direct formula. These pure finite constructions call no external source.
-/
inductive Construction (earlier : Snapshot) : Cursor.Request → Snapshot → Type where
  /-- The actual cached path owns every bit construction and its exact final enclosure. -/ | bits
      {count : Nat} (path : Geometry.CCL.Prefix.Path earlier.enclosure count) :
      Construction earlier (.bits count) (Snapshot.ofEnclosure path.result)
  /-- The original direct neighbourhood calculation owns this same actual returned box. -/ | enclosure
      (target : Fraction.Rational) (positive : 0 < target) (next : Snapshot)
      (boxEq : next.enclosure.box = earlier.accuracyBox target positive) :
      Construction earlier (.enclosure target positive) next

namespace Construction

/-- Read the number of original geometric bit steps from the retained actual path. -/
@[expose] def bitSteps {earlier : Snapshot} {request : Cursor.Request} {next : Snapshot}
    (construction : Construction earlier request next) : Nat :=
  match construction with
  | .bits path => path.stepCount
  | .enclosure _ _ _ _ => 0

/-- A direct accuracy request performs one original inner-box construction and no bit construction. -/
@[expose] def enclosureSteps {earlier : Snapshot} {request : Cursor.Request} {next : Snapshot}
    (construction : Construction earlier request next) : Nat :=
  match construction with
  | .bits _ => 0
  | .enclosure _ _ _ _ => 1

/-- Read the polynomial candidate evaluations actually cached inside this original request. -/
@[expose] def evaluationCount {earlier : Snapshot} {request : Cursor.Request} {next : Snapshot}
    (construction : Construction earlier request next) : Nat :=
  match construction with
  | .bits path => path.evaluationCount
  | .enclosure _ _ _ _ => 0

/-- Read the sum of the original finite degree bounds from those same retained searches. -/
@[expose] def evaluationBound {earlier : Snapshot} {request : Cursor.Request} {next : Snapshot}
    (construction : Construction earlier request next) : Nat :=
  match construction with
  | .bits path => path.evaluationBound
  | .enclosure _ _ _ _ => 0

/-- Actual cached polynomial evaluations satisfy their original finite candidate bounds. -/
theorem evaluationCount_le {earlier : Snapshot} {request : Cursor.Request} {next : Snapshot}
    (construction : Construction earlier request next) :
    construction.evaluationCount ≤ construction.evaluationBound := by
  cases construction with
  | bits path => exact path.evaluationCount_le
  | enclosure _ _ _ _ => exact Nat.le_refl _

/-- A bit request performs exactly the requested number of actual geometric bit constructions. -/
theorem bitSteps_eq {earlier : Snapshot} {count : Nat} {next : Snapshot}
    (construction : Construction earlier (.bits count) next) : construction.bitSteps = count := by
  cases construction with
  | bits path => exact path.stepCount_eq

end Construction

set_option genInjectivity false in
/-- One actual canonical request returns its same nested source, complete prefix payment and strict accuracy. -/
structure Result (earlier : Snapshot) (request : Cursor.Request) where
  /-- The actual next original cached checkpoint. -/ next : Snapshot
  /-- The actual original geometric construction, retained rather than rebuilt for accounting. -/ construction :
    Construction earlier request next
  /-- Every later candidate remains in the exact earlier proper source box. -/ refines :
    next.enclosure.box.Refines earlier.enclosure.box
  /-- The exact previously exposed raw word persists. -/ wordPrefix : earlier.reply.word.IsPrefix next.reply.word
  /-- A bit request pays the exact additional finite count. -/ length :
    ∀ count, request = .bits count → next.reply.word.length = earlier.reply.word.length + count
  /-- An enclosure request pays its exact strict positive squared target. -/ accurate :
    ∀ target positive, request = .enclosure target positive → next.reply.ball.radiusSq < target

/-- Execute a canonical request with the existing proper-box prefix path or the same retained chart's inner box. -/
def request (earlier : Snapshot) (request : Cursor.Request) : Result earlier request := by
  have oldWord : earlier.reply.word = earlier.enclosure.word := congrArg Reply.word earlier.replyEq
  cases request with
  | bits count =>
      let path := Geometry.CCL.Prefix.Path.build earlier.enclosure count
      exact
        { next := Snapshot.ofEnclosure path.result
          construction := .bits path
          refines := path.refines
          wordPrefix := oldWord.symm ▸ path.wordPrefix
          length := by intro requested same; cases same; exact oldWord.symm ▸ path.wordLength
          accurate := by intro _ _ impossible; nomatch impossible }
  | enclosure target positive =>
      let outer := earlier.enclosure.box
      let center := outer.midpoint
      have strict := outer.midpoint_strictContains earlier.enclosure.proper
      let budget := target / 4
      have budgetPositive : 0 < budget := Fraction.Order.Field.div_pos_direct positive (by decide)
      let inner := Rational.Box.Neighborhood.innerBox outer center strict budget budgetPositive
      have proper := Rational.Box.Neighborhood.innerBox_proper strict budgetPositive
      have refines := Rational.Box.Refinement.StrictInterior.refines
        (Rational.Box.Neighborhood.innerBox_strictInterior strict budgetPositive)
      let enclosure := earlier.enclosure.refine inner proper refines
      have accurate : inner.diagonalSq < target := by
        have paid := Rational.Box.Neighborhood.innerBox_diagonalSq_lt strict budgetPositive
        have scale : 4 * (target / 4) = target :=
          (Fraction.Field.mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne target 4 (by decide))
        exact scale ▸ paid
      exact
        { next := Snapshot.ofEnclosure enclosure
          construction := .enclosure target positive (Snapshot.ofEnclosure enclosure) rfl
          refines := refines
          wordPrefix := ⟨[], (List.Append.append_nil _).trans oldWord⟩
          length := by intro _ impossible; nomatch impossible
          accurate := by intro requested requestedPositive same; cases same; exact accurate }

namespace Snapshot

/-- Execute an actual finite canonical request path through the same original cached checkpoints. -/
@[expose] def execute : Snapshot → List Cursor.Request → Snapshot
  | snapshot, [] => snapshot
  | snapshot, request :: remaining => execute (Source.request snapshot request).next remaining

/-- Appending requests continues from the exact previously reached canonical checkpoint. -/
theorem execute_append (snapshot : Snapshot) (earlier later : List Cursor.Request) :
    snapshot.execute (earlier ++ later) = (snapshot.execute earlier).execute later := by
  induction earlier generalizing snapshot with
  | nil => rfl
  | cons request remaining induction => exact induction _

end Snapshot

/-- Read one original full path question using the same canonical request procedure. -/
@[expose] def answer (origin : Snapshot) (question : Cursor.Question) : Reply :=
  (Source.request (origin.execute question.previous) question.request).next.reply

set_option genInjectivity false in
/-- One actual canonical occurrence retains its original question, enclosure and complete cached numerical reply. -/
structure Occurrence (origin : Snapshot) where
  /-- The exact original path question at this occurrence. -/ question : Cursor.Question
  /-- The actual cached source checkpoint consumed by this original request. -/ earlier : Snapshot
  /-- The consumed checkpoint is the original adapter's state at this exact path. -/ earlierEq :
    earlier = origin.execute question.previous
  /-- The complete original request result, including its actual geometric work. -/ result :
    Result earlier question.request
  /-- The retained result was computed by the same original request procedure. -/ resultSpec :
    result = Source.request earlier question.request
  /-- The actual original checkpoint after that request. -/ snapshot : Snapshot
  /-- The saved checkpoint is this retained result's exact original return value. -/ snapshotEq : snapshot = result.next
  /-- The same exact cached numerical reply. -/ reply : Reply
  /-- The reply belongs to the actual original checkpoint. -/ replyEq : reply = snapshot.reply
  /-- The reply is the actual original pure path adapter's answer. -/ answerEq : reply = answer origin question
  /-- The exact word exposed before the request. -/ previousWord : List Bool
  /-- The actual next word retains that original prefix. -/ wordPrefix : previousWord.IsPrefix reply.word
  /-- The original additional-bit request pays its exact count. -/ length :
    ∀ count, question.request = .bits count → reply.word.length = previousWord.length + count
  /-- The original enclosure request pays its own strict squared target. -/ accurate :
    ∀ target positive, question.request = .enclosure target positive → reply.ball.radiusSq < target

namespace Occurrence

/-- Sum a displayed work quantity over the original chronological request occurrences. -/
@[expose] def workSum {origin : Snapshot} (measure : Occurrence origin → Nat) : List (Occurrence origin) → Nat
  | [] => 0
  | occurrence :: remaining => measure occurrence + workSum measure remaining

/-- Appending actual request occurrences adds their work without repeating any construction. -/
theorem workSum_append {origin : Snapshot} (measure : Occurrence origin → Nat)
    (earlier later : List (Occurrence origin)) :
    workSum measure (earlier ++ later) = workSum measure earlier + workSum measure later := by
  induction earlier with
  | nil => exact (Nat.zero_add _).symm
  | cons occurrence remaining induction =>
      exact (congrArg (fun count => measure occurrence + count) induction).trans (Nat.add_assoc _ _ _).symm

/-- Read the same original numerical exchange without recomputing any parser, chart or enclosure. -/
@[expose] def exchange {origin : Snapshot} (occurrence : Occurrence origin) : Basic.Exchange Cursor.Question Reply :=
  ⟨occurrence.question, occurrence.reply⟩

end Occurrence

set_option genInjectivity false in
/-- Actual canonical new requests bind each original path question and word to its exact preceding reply. -/
inductive Spine (origin : Snapshot) : List Cursor.Request → Reply → List (Occurrence origin) →
    List Cursor.Request → Reply → Prop where
  /-- An empty actual canonical path retains the same original reply. -/ | nil (path : List Cursor.Request)
      (reply : Reply) : Spine origin path reply [] path reply
  /-- The next actual occurrence continues the original canonical path and exposed word. -/ | cons
      (occurrence : Occurrence origin) (path : List Cursor.Request) (reply : Reply)
      (questionEq : occurrence.question.previous = path) (wordEq : occurrence.previousWord = reply.word)
      {remaining : List (Occurrence origin)} {endPath : List Cursor.Request} {endReply : Reply}
      (tail : Spine origin occurrence.question.path occurrence.reply remaining endPath endReply) :
      Spine origin path reply (occurrence :: remaining) endPath endReply

namespace Spine

/-- The actual new-request spine has exactly one occurrence per chronological path extension. -/
theorem length_path {origin : Snapshot} {path : List Cursor.Request} {reply : Reply}
    {occurrences : List (Occurrence origin)} {endPath : List Cursor.Request} {endReply : Reply}
    (spine : Spine origin path reply occurrences endPath endReply) :
    endPath.length = path.length + occurrences.length := by
  induction spine with
  | nil path _ => exact (Nat.add_zero path.length).symm
  | cons occurrence path _ questionEq _ _ induction =>
      have questionLength : occurrence.question.path.length = path.length + 1 := by
        change (occurrence.question.previous ++ [_]).length = _
        rewrite [List.Append.length_append, questionEq]
        rfl
      exact induction.trans ((congrArg (fun count => count + _) questionLength).trans
        ((Nat.add_assoc _ _ _).trans (congrArg (fun count => path.length + count) (Nat.add_comm _ _))))

/-- Append the actual next canonical occurrence at its exact original current path and reply. -/
theorem append {origin : Snapshot} {path : List Cursor.Request} {reply : Reply}
    {occurrences : List (Occurrence origin)} {endPath : List Cursor.Request} {endReply : Reply}
    (spine : Spine origin path reply occurrences endPath endReply) (occurrence : Occurrence origin)
    (questionEq : occurrence.question.previous = endPath) (wordEq : occurrence.previousWord = endReply.word) :
    Spine origin path reply (occurrences ++ [occurrence]) occurrence.question.path occurrence.reply := by
  induction spine with
  | nil path reply => exact .cons occurrence path reply questionEq wordEq (.nil _ _)
  | cons earlier path reply earlierQuestion earlierWord tail induction =>
      exact .cons earlier path reply earlierQuestion earlierWord (induction questionEq wordEq)

end Spine

set_option genInjectivity false in
/-- An actual canonical recording retains the same source path, original cached occurrences and nested-box laws. -/
structure Recording (origin : Snapshot) where
  /-- The actual current original checkpoint. -/ current : Snapshot
  /-- The actual chronological path of new requests. -/ path : List Cursor.Request
  /-- The checkpoint is the original procedure's result on that same path. -/ stateEq : current = origin.execute path
  /-- Every original or recalled occurrence in order. -/ occurrences : List (Occurrence origin)
  /-- The exact new request occurrences in order, before adding recalled repetitions. -/ spine :
    List (Occurrence origin)
  /-- The same original canonical path and complete replies form the actual new-request spine. -/ spineEq :
    Spine origin [] origin.reply spine path current.reply
  /-- Every original new request remains in the complete recorded occurrence list. -/ spineIncluded :
    ∀ occurrence ∈ spine, occurrence ∈ occurrences
  /-- Every recorded or recalled occurrence belongs to the same actual new-request spine. -/ covered :
    ∀ occurrence ∈ occurrences, occurrence ∈ spine
  /-- The actual final box retains every point constraint of the original starting source. -/ originRefines :
    current.enclosure.box.Refines origin.enclosure.box
  /-- The complete original ordered trace, cached once. -/ trace : Basic.Trace Cursor.Question Reply
  /-- The trace retains those same original occurrences. -/ traceEq : trace = occurrences.map Occurrence.exchange
  /-- The actual final proper box refines every original recorded occurrence box. -/ retained :
    ∀ occurrence ∈ occurrences, current.enclosure.box.Refines occurrence.snapshot.enclosure.box

namespace Recording

/-- Count calls to the original geometric request handler; recalls are excluded from the new-request spine. -/
@[expose] def requestCount {origin : Snapshot} (recording : Recording origin) : Nat := recording.spine.length

/-- The counted handler calls are exactly the original source's actual new-request path. -/
theorem requestCount_eq {origin : Snapshot} (recording : Recording origin) :
    recording.requestCount = recording.path.length :=
  (recording.spineEq.length_path.trans (Nat.zero_add _)).symm

/-- Count the actual retained geometric bit constructions, independently of handler calls and numerical fuel. -/
@[expose] def bitSteps {origin : Snapshot} (recording : Recording origin) : Nat :=
  Occurrence.workSum (fun occurrence => occurrence.result.construction.bitSteps) recording.spine

/-- Count the direct inner-box accuracy constructions among actual new requests. -/
@[expose] def enclosureSteps {origin : Snapshot} (recording : Recording origin) : Nat :=
  Occurrence.workSum (fun occurrence => occurrence.result.construction.enclosureSteps) recording.spine

/-- Count the polynomial candidate evaluations from the exact cached actual request results. -/
@[expose] def evaluationCount {origin : Snapshot} (recording : Recording origin) : Nat :=
  Occurrence.workSum (fun occurrence => occurrence.result.construction.evaluationCount) recording.spine

/-- Sum the original finite search bounds from those same cached actual request results. -/
@[expose] def evaluationBound {origin : Snapshot} (recording : Recording origin) : Nat :=
  Occurrence.workSum (fun occurrence => occurrence.result.construction.evaluationBound) recording.spine

/-- The actual chronological geometric searches satisfy their summed finite candidate bounds. -/
theorem evaluationCount_le {origin : Snapshot} (recording : Recording origin) :
    recording.evaluationCount ≤ recording.evaluationBound := by
  unfold evaluationCount evaluationBound
  induction recording.spine with
  | nil => exact Nat.le_refl _
  | cons occurrence remaining induction =>
      exact Nat.add_le_add occurrence.result.construction.evaluationCount_le induction

/-- Start a canonical recording at its original proper prefix enclosure with an empty path and trace. -/
def start (origin : Snapshot) : Recording origin :=
  { current := origin
    path := []
    stateEq := rfl
    occurrences := []
    spine := []
    spineEq := .nil [] origin.reply
    spineIncluded := fun _ impossible => by nomatch impossible
    covered := fun _ impossible => by nomatch impossible
    originRefines := Rational.Box.refines_refl origin.enclosure.box
    trace := []
    traceEq := rfl
    retained := fun _ impossible => by nomatch impossible }

/-- Execute one original canonical request once and retain its actual new checkpoint and complete cached reply. -/
def request {origin : Snapshot} (recording : Recording origin) (request : Cursor.Request) : Recording origin := by
  let result := Source.request recording.current request
  let question : Cursor.Question := ⟨recording.path, request⟩
  have resultEq : result.next = (Source.request (origin.execute recording.path) request).next :=
    congrArg (fun snapshot => (Source.request snapshot request).next) recording.stateEq
  let occurrence : Occurrence origin :=
    ⟨question, recording.current, recording.stateEq, result, rfl, result.next, rfl,
      result.next.reply, rfl, congrArg Snapshot.reply resultEq,
      recording.current.reply.word, result.wordPrefix, result.length, result.accurate⟩
  exact
    { current := result.next
      path := recording.path ++ [request]
      stateEq := by rewrite [Snapshot.execute_append]; exact resultEq
      occurrences := recording.occurrences ++ [occurrence]
      spine := recording.spine ++ [occurrence]
      spineEq := recording.spineEq.append occurrence rfl rfl
      spineIncluded := by
        intro entry included
        cases List.Membership.mem_append.mp included with
        | inl earlier => exact List.Membership.mem_append.mpr (.inl (recording.spineIncluded entry earlier))
        | inr final => exact List.Membership.mem_append.mpr (.inr final)
      covered := by
        intro entry included
        cases List.Membership.mem_append.mp included with
        | inl earlier => exact List.Membership.mem_append.mpr (.inl (recording.covered entry earlier))
        | inr final => exact List.Membership.mem_append.mpr (.inr final)
      originRefines := result.refines.trans recording.originRefines
      trace := recording.trace ++ [occurrence.exchange]
      traceEq := by
        rewrite [List.Map.map_append]
        exact congrArg (fun earlier => earlier ++ [occurrence.exchange]) recording.traceEq
      retained := by
        intro entry member
        cases List.Membership.mem_append.mp member with
        | inl earlier => exact result.refines.trans (recording.retained entry earlier)
        | inr final =>
            have equal := List.Membership.mem_singleton.mp final
            cases equal
            exact Rational.Box.refines_refl result.next.enclosure.box }

/-- Recall an original cached occurrence without advancing the source or changing its actual request path. -/
def recall {origin : Snapshot} (recording : Recording origin) (occurrence : Occurrence origin)
    (member : occurrence ∈ recording.occurrences) : Recording origin :=
  { current := recording.current
    path := recording.path
    stateEq := recording.stateEq
    occurrences := recording.occurrences ++ [occurrence]
    spine := recording.spine
    spineEq := recording.spineEq
    spineIncluded := fun entry included =>
      List.Membership.mem_append.mpr (.inl (recording.spineIncluded entry included))
    covered := by
      intro entry included
      cases List.Membership.mem_append.mp included with
      | inl earlier => exact recording.covered entry earlier
      | inr final =>
          have equal := List.Membership.mem_singleton.mp final
          cases equal
          exact recording.covered occurrence member
    originRefines := recording.originRefines
    trace := recording.trace ++ [occurrence.exchange]
    traceEq := by
      rewrite [List.Map.map_append]
      exact congrArg (fun earlier => earlier ++ [occurrence.exchange]) recording.traceEq
    retained := by
      intro entry included
      cases List.Membership.mem_append.mp included with
      | inl earlier => exact recording.retained entry earlier
      | inr final =>
          have equal := List.Membership.mem_singleton.mp final
          cases equal
          exact recording.retained occurrence member }

/-- Each new request calls the original geometric handler exactly once. -/
theorem request_count {origin : Snapshot} (recording : Recording origin) (request : Cursor.Request) :
    (recording.request request).requestCount = recording.requestCount + 1 :=
  List.Append.length_append recording.spine _

/-- A new request adds exactly its retained geometric bit work. -/
theorem request_bitSteps {origin : Snapshot} (recording : Recording origin) (request : Cursor.Request) :
    (recording.request request).bitSteps =
      recording.bitSteps + (Source.request recording.current request).construction.bitSteps := by
  change Occurrence.workSum _ (recording.spine ++ [_]) = _
  rewrite [Occurrence.workSum_append]
  exact congrArg (fun count => recording.bitSteps + count) (Nat.add_zero _)

/-- A new accuracy construction adds its original direct inner-box work. -/
theorem request_enclosureSteps {origin : Snapshot} (recording : Recording origin) (request : Cursor.Request) :
    (recording.request request).enclosureSteps =
      recording.enclosureSteps + (Source.request recording.current request).construction.enclosureSteps := by
  change Occurrence.workSum _ (recording.spine ++ [_]) = _
  rewrite [Occurrence.workSum_append]
  exact congrArg (fun count => recording.enclosureSteps + count) (Nat.add_zero _)

/-- A new request adds exactly the polynomial evaluations cached by its original geometric searches. -/
theorem request_evaluationCount {origin : Snapshot} (recording : Recording origin) (request : Cursor.Request) :
    (recording.request request).evaluationCount =
      recording.evaluationCount + (Source.request recording.current request).construction.evaluationCount := by
  change Occurrence.workSum _ (recording.spine ++ [_]) = _
  rewrite [Occurrence.workSum_append]
  exact congrArg (fun count => recording.evaluationCount + count) (Nat.add_zero _)

/-- Recalling a saved reply preserves every original construction and adds no handler or geometric work. -/
theorem recall_work {origin : Snapshot} (recording : Recording origin)
    (occurrence : Occurrence origin) (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).requestCount = recording.requestCount ∧
      (recording.recall occurrence member).bitSteps = recording.bitSteps ∧
      (recording.recall occurrence member).enclosureSteps = recording.enclosureSteps ∧
      (recording.recall occurrence member).evaluationCount = recording.evaluationCount ∧
      (recording.recall occurrence member).evaluationBound = recording.evaluationBound :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The canonical recording constructor retains its exact empty request path and trace. -/
private theorem start_specification (origin : Snapshot) :
    (start origin).path = [] ∧ (start origin).trace = [] := ⟨rfl, rfl⟩

/-- A newly started canonical recording has no requests in its actual path. -/
theorem start_path (origin : Snapshot) : (start origin).path = [] := (start_specification origin).1

/-- A newly started canonical recording has an empty ordered numerical trace. -/
theorem start_trace (origin : Snapshot) : (start origin).trace = [] := (start_specification origin).2

/-- A canonical request retains its exact next path, appended complete reply and original pure answer. -/
private theorem request_specification {origin : Snapshot} (recording : Recording origin) (request : Cursor.Request) :
    (recording.request request).path = recording.path ++ [request] ∧
      (recording.request request).trace = recording.trace ++
        [⟨⟨recording.path, request⟩, (recording.request request).current.reply⟩] ∧
      (recording.request request).current.reply = answer origin ⟨recording.path, request⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  exact congrArg Snapshot.reply
    (congrArg (fun snapshot => (Source.request snapshot request).next) recording.stateEq)

/-- An actual canonical request appends its original tagged request to the same cached path. -/
theorem request_path {origin : Snapshot} (recording : Recording origin) (request : Cursor.Request) :
    (recording.request request).path = recording.path ++ [request] := (request_specification recording request).1

/-- An actual canonical request appends its same cached complete numerical reply at the original path question. -/
theorem request_trace {origin : Snapshot} (recording : Recording origin) (request : Cursor.Request) :
    (recording.request request).trace = recording.trace ++
      [⟨⟨recording.path, request⟩, (recording.request request).current.reply⟩] :=
  (request_specification recording request).2.1

/-- An actual canonical request returns exactly the pure path adapter's same original numerical answer. -/
theorem request_reply {origin : Snapshot} (recording : Recording origin) (request : Cursor.Request) :
    (recording.request request).current.reply = answer origin ⟨recording.path, request⟩ :=
  (request_specification recording request).2.2

/-- A canonical recall retains the same path and appends the same original complete exchange. -/
private theorem recall_specification {origin : Snapshot} (recording : Recording origin)
    (occurrence : Occurrence origin) (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).path = recording.path ∧
      (recording.recall occurrence member).trace = recording.trace ++ [occurrence.exchange] := ⟨rfl, rfl⟩

/-- Recalling a canonical occurrence leaves the actual new-request path unchanged. -/
theorem recall_path {origin : Snapshot} (recording : Recording origin)
    (occurrence : Occurrence origin) (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).path = recording.path := (recall_specification recording occurrence member).1

/-- Recalling a canonical occurrence appends its same exact original exchange. -/
theorem recall_trace {origin : Snapshot} (recording : Recording origin)
    (occurrence : Occurrence origin) (member : occurrence ∈ recording.occurrences) :
    (recording.recall occurrence member).trace = recording.trace ++ [occurrence.exchange] :=
  (recall_specification recording occurrence member).2

/-- Every actual canonical exchange is the same complete numerical reply of the original pure path adapter. -/
theorem answers {origin : Snapshot} (recording : Recording origin) : Basic.Answers (answer origin) recording.trace := by
  intro entry member
  have mapped : entry ∈ recording.occurrences.map Occurrence.exchange := recording.traceEq ▸ member
  rcases List.Map.mem_map.mp mapped with ⟨occurrence, _included, rfl⟩
  exact occurrence.answerEq.symm

/-- Execute a finite mixed request list through the actual canonical recording and its exact caches. -/
def execute {origin : Snapshot} : Recording origin → List Cursor.Request → Recording origin
  | recording, [] => recording
  | recording, request :: remaining => execute (recording.request request) remaining

/-- Continuing with an appended request list uses the exact previously returned recording. -/
theorem execute_append {origin : Snapshot} (recording : Recording origin)
    (earlier later : List Cursor.Request) :
    recording.execute (earlier ++ later) = (recording.execute earlier).execute later := by
  induction earlier generalizing recording with
  | nil => rfl
  | cons request remaining induction => exact induction _

/-- The actual longer recording retains every old numerical exchange in its original order. -/
theorem execute_tracePrefix {origin : Snapshot} (recording : Recording origin)
    (requests : List Cursor.Request) : recording.trace.IsPrefix (recording.execute requests).trace := by
  induction requests generalizing recording with
  | nil => exact ⟨[], List.Append.append_nil _⟩
  | cons request remaining induction =>
      rcases induction (recording.request request) with ⟨suffix, suffixEq⟩
      let entry : Basic.Exchange Cursor.Question Reply :=
        ⟨⟨recording.path, request⟩, (recording.request request).current.reply⟩
      refine ⟨entry :: suffix, ?_⟩
      exact (List.Append.append_assoc recording.trace [entry] suffix).symm.trans
        ((congrArg (fun earlier => earlier ++ suffix) (recording.request_trace request).symm).trans suffixEq)

/-- The actual returned request path extends the original path by precisely the supplied requests. -/
theorem execute_path {origin : Snapshot} (recording : Recording origin)
    (requests : List Cursor.Request) : (recording.execute requests).path = recording.path ++ requests := by
  induction requests generalizing recording with
  | nil => exact (List.Append.append_nil _).symm
  | cons request remaining induction =>
      exact (induction (recording.request request)).trans
        ((congrArg (fun path => path ++ remaining) (recording.request_path request)).trans
          (List.Append.append_assoc recording.path [request] remaining))

/-- Realize one original cached canonical exchange at the actual final proper-box survivor. -/
private def realizeOccurrence {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) (occurrence : Occurrence origin)
    (member : occurrence ∈ recording.occurrences) : Realization occurrence.exchange realization.point := by
  have inside := (recording.retained occurrence member).contains realization.sample.inside
  let candidate := Reply.candidateOfEnclosure occurrence.snapshot.enclosure realization.point inside
  have replyEq : occurrence.reply = Reply.ofEnclosure occurrence.snapshot.enclosure :=
    occurrence.replyEq.trans occurrence.snapshot.replyEq
  exact
    { candidate := by
        change Reply.Candidate occurrence.reply realization.point
        exact replyEq.symm ▸ candidate
      previousWord := occurrence.previousWord
      wordPrefix := occurrence.wordPrefix
      length := occurrence.length
      accurate := occurrence.accurate }

/-- Cache every original exchange's realization against the same final proper-box sample, in its original order. -/
private def realizeOccurrences {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) :
    (occurrences : List (Occurrence origin)) → (∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences) →
      List ((entry : Basic.Exchange Cursor.Question Reply) × Realization entry realization.point)
  | [], _ => []
  | occurrence :: remaining, retained =>
      ⟨occurrence.exchange, realizeOccurrence recording realization occurrence
        (retained occurrence (List.Mem.head remaining))⟩ :: realizeOccurrences recording realization remaining
          (fun entry member => retained entry (List.Mem.tail occurrence member))

/-- Realization production preserves the exact original ordered canonical trace, including recalled occurrences. -/
private theorem realizeOccurrences_projection {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) :
    (occurrences : List (Occurrence origin)) →
      (retained : ∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences) →
      (realizeOccurrences recording realization occurrences retained).map Sigma.fst =
        occurrences.map Occurrence.exchange
  | [], _ => rfl
  | occurrence :: remaining, retained =>
      congrArg (List.cons occurrence.exchange) (realizeOccurrences_projection recording realization remaining
        (fun entry member => retained entry (List.Mem.tail occurrence member)))

/-- Describe one original canonical occurrence using its same cached affine candidate and complete numerical reply. -/
private def codeOfOccurrence {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) (occurrence : Occurrence origin)
    (member : occurrence ∈ recording.occurrences) : {code : Continuation.Code // code.Valid} :=
  let certified := realizeOccurrence recording realization occurrence member
  Continuation.Code.ofCandidate occurrence.reply realization.point certified.candidate

/-- The same canonical occurrence description retains its original reply and the exact common rational reading. -/
private theorem codeOfOccurrence_specification {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) (occurrence : Occurrence origin)
    (member : occurrence ∈ recording.occurrences) :
    (codeOfOccurrence recording realization occurrence member).val.point = realization.point ∧
      (codeOfOccurrence recording realization occurrence member).val.reply = occurrence.reply := ⟨rfl, rfl⟩

/-- Cache the exact new-request canonical codes, keeping recalled repetitions in their separate complete trace. -/
private def spineCodes {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) :
    (occurrences : List (Occurrence origin)) → (∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences) →
      List Continuation.Step
  | [], _ => []
  | occurrence :: remaining, retained =>
      let certified := codeOfOccurrence recording realization occurrence (retained occurrence (List.Mem.head remaining))
      ⟨occurrence.question.request, certified.val⟩ :: spineCodes recording realization remaining
        (fun entry member => retained entry (List.Mem.tail occurrence member))

/-- Realizing the actual canonical source spine preserves each exact preceding code and complete request payment. -/
private theorem spineCodes_chain {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization)
    {path : List Cursor.Request} {reply : Reply} {occurrences : List (Occurrence origin)}
    {endPath : List Cursor.Request} {endReply : Reply} (spine : Spine origin path reply occurrences endPath endReply)
    (retained : ∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences)
    (earlier : Continuation.Code) (pointEq : earlier.point = realization.point) (replyEq : earlier.reply = reply) :
    Continuation.Chain earlier (spineCodes recording realization occurrences retained) := by
  induction spine generalizing earlier with
  | nil path reply => exact .nil earlier
  | cons occurrence path reply questionEq wordEq tail induction =>
      let member := retained occurrence (List.Mem.head _)
      let certified := codeOfOccurrence recording realization occurrence member
      have specification := codeOfOccurrence_specification recording realization occurrence member
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

/-- The realized canonical spine retains exactly the original new-request questions and numerical replies. -/
private theorem spineCodes_trace {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization)
    {path : List Cursor.Request} {reply : Reply} {occurrences : List (Occurrence origin)}
    {endPath : List Cursor.Request} {endReply : Reply} (spine : Spine origin path reply occurrences endPath endReply)
    (retained : ∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences) :
    Continuation.History.traceFrom path (spineCodes recording realization occurrences retained) =
      occurrences.map Occurrence.exchange := by
  induction spine with
  | nil path reply => rfl
  | cons occurrence path reply questionEq wordEq tail induction =>
      have specification := codeOfOccurrence_specification recording realization occurrence
        (retained occurrence (List.Mem.head _))
      have actualQuestion : Path.Question.mk path occurrence.question.request = occurrence.question :=
        congrArg (fun previous => Path.Question.mk previous occurrence.question.request) questionEq.symm
      have actualPath : path ++ [occurrence.question.request] = occurrence.question.path :=
        congrArg (fun previous => previous ++ [occurrence.question.request]) questionEq.symm
      refine congrArg₂ List.cons ?_ ?_
      · change (⟨⟨path, occurrence.question.request⟩, _⟩ : Basic.Exchange Cursor.Question Reply) = occurrence.exchange
        rewrite [specification.2, actualQuestion]
        rfl
      · exact actualPath.symm ▸ induction (fun entry member => retained entry (List.Mem.tail occurrence member))

/-- The saved codes retain exactly the actual chronological request path. -/
private theorem spineCodes_requests {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization)
    {path : List Cursor.Request} {reply : Reply} {occurrences : List (Occurrence origin)}
    {endPath : List Cursor.Request} {endReply : Reply} (spine : Spine origin path reply occurrences endPath endReply)
    (retained : ∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences) :
    path ++ (spineCodes recording realization occurrences retained).map
      (fun step : Continuation.Step => step.request) = endPath := by
  induction spine with
  | nil path reply => exact List.Append.append_nil _
  | @cons occurrence path reply questionEq wordEq remaining endPath endReply tail induction =>
      have actualPath : path ++ [occurrence.question.request] = occurrence.question.path :=
        congrArg (fun previous => previous ++ [occurrence.question.request]) questionEq.symm
      change path ++ (occurrence.question.request ::
        (spineCodes recording realization remaining
          (fun entry member => retained entry (List.Mem.tail occurrence member))).map
            (fun step : Continuation.Step => step.request)) = endPath
      exact (List.Append.append_assoc path [occurrence.question.request] _).symm.trans
        ((congrArg (fun previous => previous ++ _) actualPath).trans
          (induction (fun entry member => retained entry (List.Mem.tail occurrence member))))

/-- Reading the last saved spine code returns its actual original final numerical reply. -/
private theorem spineCodes_endpoint {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization)
    {path : List Cursor.Request} {reply : Reply} {occurrences : List (Occurrence origin)}
    {endPath : List Cursor.Request} {endReply : Reply} (spine : Spine origin path reply occurrences endPath endReply)
    (retained : ∀ occurrence ∈ occurrences, occurrence ∈ recording.occurrences)
    (earlier : Continuation.Code) (replyEq : earlier.reply = reply) :
    (Continuation.History.endpointFrom earlier (spineCodes recording realization occurrences retained)).reply =
      endReply := by
  induction spine generalizing earlier with
  | nil path reply => exact replyEq
  | cons occurrence path reply questionEq wordEq tail induction =>
      exact induction (fun entry member => retained entry (List.Mem.tail occurrence member))
        (codeOfOccurrence recording realization occurrence (retained occurrence (List.Mem.head _))).val
        (codeOfOccurrence_specification recording realization occurrence
          (retained occurrence (List.Mem.head _))).2

/-- The last original reply and its validity bind every saved cursor cache to the retained final realization. -/
private theorem endpoint_cursor (snapshot : Snapshot) (realization : snapshot.enclosure.Realization)
    (code : Continuation.Code) (valid : code.Valid) (replyEq : code.reply = snapshot.reply)
    (pointEq : code.point = realization.point) :
    code.cursor = (Encoding.Prefix.Cursor.ofRealization realization).val := by
  have numerical : code.reply = Reply.ofEnclosure snapshot.enclosure := replyEq.trans snapshot.replyEq
  have wordEq : code.cursor.word = snapshot.enclosure.word :=
    valid.wordEq.symm.trans (congrArg Reply.word numerical)
  have stateEq : code.cursor.state = snapshot.enclosure.state :=
    valid.stateEq.symm.trans (congrArg Reply.state numerical)
  have inverseEq : code.cursor.inverseMatrix = snapshot.enclosure.inverseMatrix :=
    valid.inverseEq.symm.trans (congrArg Reply.inverseMatrix numerical)
  have tailEq : code.cursor.tail = realization.tail := valid.cursor.tailSpec.trans
    ((congrArg₂ Projective.Homography.Basic.homographic inverseEq pointEq).trans realization.tailSpec.symm)
  cases code with
  | mk cursor reply =>
      cases cursor with
      | mk point word state inverse tail =>
          change point = realization.point at pointEq
          change word = snapshot.enclosure.word at wordEq
          change state = snapshot.enclosure.state at stateEq
          change inverse = snapshot.enclosure.inverseMatrix at inverseEq
          change tail = realization.tail at tailEq
          cases pointEq
          cases wordEq
          cases stateEq
          cases inverseEq
          cases tailEq
          rfl

/-- Produce canonical admission from a supplied final-box realization and the complete nested request spine.

The same final proper box uniformly satisfies every recorded ball and exact
raw prefix. Each earlier affine tail consumes its original inverse-chart
cache; no independent rational encoding is substituted for the exposed word.
-/
def admitWith {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) : Admitted recording.trace := by
  let exchanges := realizeOccurrences recording realization recording.occurrences (fun _ member => member)
  have originInside := recording.originRefines.contains realization.sample.inside
  let originalCandidate := Reply.candidateOfEnclosure origin.enclosure realization.point originInside
  let initialCandidate : Reply.Candidate origin.reply realization.point := origin.replyEq.symm ▸ originalCandidate
  let initialCode := Continuation.Code.ofCandidate origin.reply realization.point initialCandidate
  let steps := spineCodes recording realization recording.spine recording.spineIncluded
  let history : Continuation.History := ⟨initialCode.val, steps⟩
  have savedTrace : history.trace = recording.spine.map Occurrence.exchange :=
    spineCodes_trace recording realization recording.spineEq recording.spineIncluded
  have historyValid : history.Valid := ⟨initialCode.property,
    spineCodes_chain recording realization recording.spineEq recording.spineIncluded initialCode.val rfl rfl⟩
  let endpoint := history.endpoint
  have endpointReply : endpoint.reply = recording.current.reply :=
    spineCodes_endpoint recording realization recording.spineEq recording.spineIncluded initialCode.val rfl
  have endpointPoint : endpoint.point = realization.point := history.endpoint_point historyValid
  have endpointCursor := endpoint_cursor recording.current realization endpoint
    (history.endpoint_valid historyValid) endpointReply endpointPoint
  exact
    { enclosure := recording.current.enclosure
      realization := realization
      exchanges := exchanges
      traceEq := (realizeOccurrences_projection recording realization recording.occurrences
        (fun _ member => member)).trans recording.traceEq.symm
      uniform := by
        intro point inside entry member
        have mapped : entry ∈ recording.occurrences.map Occurrence.exchange := recording.traceEq ▸ member
        rcases List.Map.mem_map.mp mapped with ⟨occurrence, retained, rfl⟩
        have earlierInside := (recording.retained occurrence retained).contains inside
        have replyEq := occurrence.replyEq.trans occurrence.snapshot.replyEq
        change occurrence.reply.ball.Contains point ∧ Parser.Semantics.Prefix.Represented occurrence.reply.word point
        rewrite [replyEq]
        exact ⟨occurrence.snapshot.enclosure.box.inside_enclosure earlierInside,
          occurrence.snapshot.enclosure.represented earlierInside⟩
      accurate := by
        intro entry member
        have mapped : entry ∈ recording.occurrences.map Occurrence.exchange := recording.traceEq ▸ member
        rcases List.Map.mem_map.mp mapped with ⟨occurrence, _retained, rfl⟩
        exact occurrence.accurate
      history := history
      historyValid := historyValid
      historyPoint := rfl
      endpoint := endpoint
      endpointEq := rfl
      endpointCursor := endpointCursor
      covered := by
        intro entry member
        have mapped : entry ∈ recording.occurrences.map Occurrence.exchange := recording.traceEq ▸ member
        rcases List.Map.mem_map.mp mapped with ⟨occurrence, included, rfl⟩
        exact savedTrace.symm ▸ List.Map.mem_map.mpr ⟨occurrence, recording.covered occurrence included, rfl⟩
      consistent := by
        intro left leftMember right rightMember same
        exact (recording.answers left leftMember).symm.trans
          ((congrArg (answer origin) same).trans (recording.answers right rightMember)) }

private theorem admitWith_point_specification {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) :
    (recording.admitWith realization).realization.point = realization.point := rfl

/-- Admission with a supplied final-box realization preserves that same cached rational reading. -/
theorem admitWith_point {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) :
    (recording.admitWith realization).realization.point = realization.point :=
  admitWith_point_specification recording realization

/-- The original admitted history retains the actual source recording's complete request path. -/
theorem admitWith_path {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) :
    (recording.admitWith realization).history.steps.map (fun step : Continuation.Step => step.request) =
      recording.path :=
  spineCodes_requests recording realization recording.spineEq recording.spineIncluded

/-- The original admitted endpoint retains the same exact final numerical reply, including its ambient ball. -/
theorem admitWith_endpoint_reply {origin : Snapshot} (recording : Recording origin)
    (realization : recording.current.enclosure.Realization) :
    (recording.admitWith realization).endpoint.reply = recording.current.reply :=
  spineCodes_endpoint recording realization recording.spineEq recording.spineIncluded _ rfl

/-- Admit the complete actual request spine at the final enclosure's original deterministic rational sample. -/
def admission {origin : Snapshot} (recording : Recording origin) : Admitted recording.trace :=
  recording.admitWith recording.current.enclosure.realize

/-- Execute and admit one actual canonical mixed request list without repeating the source path construction. -/
def admitRequests (origin : Snapshot) (requests : List Cursor.Request) :
    (recording : Recording origin) × Admitted recording.trace :=
  let recording := (start origin).execute requests
  ⟨recording, recording.admission⟩

/-- Extend an actual source recording once and retain the rational continuation of that same longer history.

The returned recording is the actual source procedure's result, including its
new nested boxes and exact old numerical replies. Its admission chooses the
longer history's cached proper-box sample; the earlier rational reading need
not remain the same when the source is queried again.
-/
def continueRequests {origin : Snapshot} (recording : Recording origin) (requests : List Cursor.Request) :
    (longer : Recording origin) × Continuation.Result longer.trace :=
  let longer := recording.execute requests
  ⟨longer, Continuation.ofAdmitted longer.admission⟩

/-- Extending and continuing retains the actual source procedure's returned recording. -/
private theorem continueRequests_recording_specification {origin : Snapshot} (recording : Recording origin)
    (requests : List Cursor.Request) : (recording.continueRequests requests).fst = recording.execute requests := rfl

/-- The returned continuation owns the actual source endpoint reached by the supplied further requests. -/
theorem continueRequests_recording {origin : Snapshot} (recording : Recording origin)
    (requests : List Cursor.Request) : (recording.continueRequests requests).fst = recording.execute requests :=
  continueRequests_recording_specification recording requests

/-- The same longer continuation reproduces every exact reply in the original earlier recording. -/
theorem continueRequests_answers {origin : Snapshot} (recording : Recording origin)
    (requests : List Cursor.Request) :
    Basic.Answers ((recording.continueRequests requests).snd.history.interpret
      (recording.continueRequests requests).snd.valid) recording.trace := by
  intro entry member
  rcases recording.execute_tracePrefix requests with ⟨suffix, suffixEq⟩
  exact (recording.continueRequests requests).snd.answers entry
    (suffixEq ▸ List.Membership.mem_append.mpr (.inl member))

/-- Extending in two actual source stages returns the same complete longer recording and rational continuation. -/
theorem continueRequests_append {origin : Snapshot} (recording : Recording origin)
    (earlier later : List Cursor.Request) :
    recording.continueRequests (earlier ++ later) =
      (recording.continueRequests earlier).fst.continueRequests later := by
  unfold continueRequests
  exact congrArg (fun longer : Recording origin =>
    (⟨longer, Continuation.ofAdmitted longer.admission⟩ :
      (longer : Recording origin) × Continuation.Result longer.trace)) (recording.execute_append earlier later)

/-- The rational continuation of the actual longer recording preserves an earlier complete adaptive execution. -/
theorem continueRequests_same_execution {origin : Snapshot} (recording : Recording origin)
    (requests : List Cursor.Request) {Value : Type} (protocol : Protocol Cursor.Question Reply Value)
    (oracle : Cursor.Question → Reply) (traceEq : (protocol.run oracle).trace = recording.trace) :
    protocol.run ((recording.continueRequests requests).snd.history.interpret
      (recording.continueRequests requests).snd.valid) = protocol.run oracle := by
  apply protocol.run_of_answers
  intro entry member
  exact recording.continueRequests_answers requests entry (traceEq ▸ member)

end Recording

end Source

end Purelib.Approximation.Gaussian.Observation.Prefix

end
