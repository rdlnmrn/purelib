module

public import Purelib.Computation.Query.Basic
public import Purelib.Computation.Query.Path
import Purelib.Data.List.Append
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
public import Purelib.Data.List.All

/-!
# Chronological saved request histories

Each saved request retains its original next code. Indexed chains attach
transition certificates to the actual preceding code, and checking retains
the original suffix of the first defect. Containment completion and replay
consume these same stored codes rather than rebuilding them.
-/

public section

namespace Purelib.Computation.Query

open Purelib.Data

universe u v w x

namespace History

set_option genInjectivity false in
/-- One original request and the complete code saved after answering it. -/
structure Step (Request : Type u) (Code : Type v) where
  /-- The exact original tagged request. -/ request : Request
  /-- The complete retained next code. -/ next : Code

set_option genInjectivity false in
/-- A chronological chain certifies every saved step from its exact preceding code.

The transition predicate retains its original code and saved step arguments.
Each successor starts its suffix at that same step's cached next code.
-/
inductive Chain {Request : Type u} {Code : Type v}
    (valid : Code → Step Request Code → Prop) : Code → List (Step Request Code) → Prop where
  /-- No request changes the supplied current code. -/ | nil (code : Code) : Chain valid code []
  /-- A certified saved transition consumes the current code and continues its original suffix. -/ | cons
      {earlier : Code} (step : Step Request Code) {remaining : List (Step Request Code)}
      (head : valid earlier step) (tail : Chain valid step.next remaining) :
      Chain valid earlier (step :: remaining)

/-- Read the last retained code without executing or rebuilding any saved transition. -/
@[expose] def finish {Request : Type u} {Code : Type v} : Code → List (Step Request Code) → Code
  | earlier, [] => earlier
  | _, step :: remaining => finish step.next remaining

/-- Appending saved steps starts from the same literal retained preceding endpoint. -/
theorem finish_append {Request : Type u} {Code : Type v} (earlier : Code)
    (first later : List (Step Request Code)) :
    finish earlier (first ++ later) = finish (finish earlier first) later := by
  induction first generalizing earlier with
  | nil => rfl
  | cons step remaining induction => exact induction step.next

namespace Chain

variable {Request : Type u} {Code : Type v} {valid : Code → Step Request Code → Prop}

/-- Append a certified saved suffix at the exact retained endpoint of the original chain. -/
theorem append {earlier : Code} {first later : List (Step Request Code)}
    (before : Chain valid earlier first) (after : Chain valid (finish earlier first) later) :
    Chain valid earlier (first ++ later) := by
  induction before with
  | nil code => exact after
  | cons step head tail induction => exact .cons step head (induction after)

/-- Project the first saved transition's exact preceding-code certificate. -/
theorem head {earlier : Code} {step : Step Request Code} {remaining : List (Step Request Code)}
    (chain : Chain valid earlier (step :: remaining)) : valid earlier step := by
  cases chain with | cons _ head _ => exact head

/-- Project the original saved suffix starting at the same cached next code. -/
theorem tail {earlier : Code} {step : Step Request Code} {remaining : List (Step Request Code)}
    (chain : Chain valid earlier (step :: remaining)) : Chain valid step.next remaining := by
  cases chain with | cons _ _ tail => exact tail

/-- Transport transition certificates without changing any retained request or code. -/
theorem map {other : Code → Step Request Code → Prop}
    (transport : ∀ earlier step, valid earlier step → other earlier step)
    {earlier : Code} {steps : List (Step Request Code)} (chain : Chain valid earlier steps) :
    Chain other earlier steps := by
  induction chain with
  | nil code => exact .nil code
  | cons step head tail induction => exact .cons step (transport _ step head) induction

/-- A propagated code condition holds at every chronological retained code.

The initial condition and each exact transition determine the condition at
its cached next code. Membership retains order and repeated code occurrences.
-/
theorem all (condition : Code → Prop)
    (advance : ∀ earlier step, valid earlier step → condition step.next)
    (earlier : Code) (initial : condition earlier) (steps : List (Step Request Code))
    (chain : Chain valid earlier steps) :
    ∀ code ∈ earlier :: steps.map Step.next, condition code := by
  induction chain with
  | nil code =>
      intro entry member
      have equal := List.Membership.mem_singleton.mp member
      cases equal
      exact initial
  | cons step head tail induction =>
      intro code member
      cases List.Membership.mem_cons.mp member with
      | inl equal => cases equal; exact initial
      | inr later => exact induction (advance _ step head) code later

/-- Complete each retained transition using additional evidence for its exact cached next code. -/
theorem complete {other : Code → Step Request Code → Prop} (condition : Code → Prop)
    (finish : ∀ earlier step, valid earlier step → condition step.next → other earlier step)
    {earlier : Code} {steps : List (Step Request Code)} (chain : Chain valid earlier steps)
    (evidence : ∀ code ∈ steps.map Step.next, condition code) : Chain other earlier steps := by
  induction chain with
  | nil code => exact .nil code
  | cons step head tail induction =>
      exact .cons step (finish _ step head (evidence step.next (List.Mem.head _)))
        (induction (fun code member => evidence code (List.Mem.tail step.next member)))

set_option genInjectivity false in
/-- A chronological defect retains the actual preceding code and original failing suffix. -/
inductive Invalid (reason : Code → Step Request Code → Type w) :
    Code → List (Step Request Code) → Type (max u v w) where
  /-- The first saved request has this exact defect. -/ | head {earlier : Code} (step : Step Request Code)
      {remaining : List (Step Request Code)} (failed : reason earlier step) :
      Invalid reason earlier (step :: remaining)
  /-- A later defect retains the original intervening saved request. -/ | tail {earlier : Code}
      (step : Step Request Code) {remaining : List (Step Request Code)}
      (failed : Invalid reason step.next remaining) : Invalid reason earlier (step :: remaining)

namespace Invalid

/-- Every retained defect refutes certification of that exact chronological chain. -/
theorem refutes {reason : Code → Step Request Code → Type w}
    (refute : ∀ earlier step, reason earlier step → ¬ valid earlier step)
    {earlier : Code} {steps : List (Step Request Code)} (invalid : Invalid reason earlier steps) :
    ¬ Chain valid earlier steps := by
  intro prepared
  induction invalid with
  | head step reason => cases prepared with | cons _ head _ => exact refute _ step reason head
  | tail step reason induction => cases prepared with | cons _ _ tail => exact induction tail

end Invalid

/-- Check saved transitions once in chronological order and retain the original first failing suffix.

The supplied checker returns either the exact transition certificate or its
indexed defect. Each saved step is checked once; a failure stops traversal
and retains every intervening original step and the actual failing suffix.
-/
def check {reason : Code → Step Request Code → Type w}
    (checkStep : (earlier : Code) → (step : Step Request Code) →
      Except (reason earlier step) (PLift (valid earlier step))) :
    (earlier : Code) → (steps : List (Step Request Code)) →
      Except (Invalid reason earlier steps) (PLift (Chain valid earlier steps))
  | earlier, [] => .ok ⟨.nil earlier⟩
  | earlier, step :: remaining =>
      match checkStep earlier step with
      | .error reason => .error (.head step reason)
      | .ok head =>
          match check checkStep step.next remaining with
          | .error reason => .error (.tail step reason)
          | .ok tail => .ok ⟨.cons step head.down tail.down⟩

end Chain

set_option genInjectivity false in
/-- A saved-history interpreter retains its current valid code and exact unconsumed certified suffix.

The current intrinsic certificate and saved-chain index concern the same code.
Its suffix contains the original stored requests and next-code caches.
-/
structure State {Request : Type u} {Code : Type v} (validCode : Code → Prop)
    (validStep : Code → Step Request Code → Prop) where
  /-- The actual retained current code. -/ code : Code
  /-- The current code has its original intrinsic validity. -/ valid : validCode code
  /-- The saved requests still available on this same path. -/ remaining : List (Step Request Code)
  /-- The remaining requests begin at this exact current code. -/ chain : Chain validStep code remaining

/-- Execute a finite request path by consuming each actual preceding state.

The empty path returns the original state. Each supplied transition consumes
its actual preceding state and passes that returned state directly to the
remaining chronological requests.
-/
@[expose] def execute {Request : Type u} {State : Type v} (step : State → Request → State) :
    State → List Request → State
  | state, [] => state
  | state, request :: remaining => execute step (step state request) remaining

/-- Appending a request path continues from its actual previously executed state. -/
theorem execute_append {Request : Type u} {State : Type v} (step : State → Request → State)
    (state : State) (earlier later : List Request) :
    execute step state (earlier ++ later) = execute step (execute step state earlier) later := by
  induction earlier generalizing state with
  | nil => rfl
  | cons request rest induction => exact induction _

/-- A preserved scalar reading remains identical after every finite request path.

The same reading projection and transition-preservation law apply at each
intermediate state. Structural path induction retains the original reading
for arbitrary finite paths, including the empty path.
-/
theorem execute_reading {Request : Type u} {State : Type v} {Reading : Type w} (step : State → Request → State)
    (reading : State → Reading) (preserves : ∀ state request, reading (step state request) = reading state)
    (state : State) (requests : List Request) : reading (execute step state requests) = reading state := by
  induction requests generalizing state with
  | nil => rfl
  | cons request rest induction => exact (induction (step state request)).trans (preserves state request)

end History

set_option genInjectivity false in
/-- A finite history stores its original initial code and complete chronological saved requests.

The request and code carriers remain independent nominal owners. No intrinsic
validity or interpretation is inferred merely from these retained data.
-/
structure History (Request : Type u) (Code : Type v) where
  /-- The same original initial code. -/ initial : Code
  /-- The saved requests with their exact cached next codes. -/ steps : List (History.Step Request Code)

namespace History

set_option genInjectivity false in
/-- A retained history has valid initial code and a chain certified from that exact code. -/
structure Valid {Request : Type u} {Code : Type v} (validCode : Code → Prop)
    (validStep : Code → Step Request Code → Prop) (history : History Request Code) : Prop where
  /-- The original initial code has intrinsic validity. -/ initial : validCode history.initial
  /-- Every saved request consumes its exact preceding code. -/ chain : Chain validStep history.initial history.steps

set_option genInjectivity false in
/-- A history defect identifies its original initial-code failure or chronological request-chain failure.

The supplied defect families keep their representation-specific conditions.
Chain defects retain the actual original preceding code and failing suffix.
-/
inductive Invalid {Request : Type u} {Code : Type v} (invalidCode : Code → Type w)
    (invalidStep : Code → Step Request Code → Type x) (history : History Request Code) where
  /-- The same supplied initial code has this identified defect. -/ | initial (reason : invalidCode history.initial)
  /-- The original chronological saved chain has this identified defect. -/ | chain
      (reason : Chain.Invalid invalidStep history.initial history.steps)

namespace Invalid

/-- Every identified history defect refutes independent certification of that exact supplied history. -/
theorem refutes {Request : Type u} {Code : Type v} {preparedCode : Code → Prop}
    {preparedStep : Code → Step Request Code → Prop} {invalidCode : Code → Type w}
    {invalidStep : Code → Step Request Code → Type x}
    (refuteCode : ∀ code, invalidCode code → ¬ preparedCode code)
    (refuteStep : ∀ earlier step, invalidStep earlier step → ¬ preparedStep earlier step)
    {history : History Request Code} (invalid : Invalid invalidCode invalidStep history) :
    ¬ Valid preparedCode preparedStep history := by
  intro prepared
  cases invalid with
  | initial reason => exact refuteCode history.initial reason prepared.initial
  | chain reason => exact Chain.Invalid.refutes refuteStep reason prepared.chain

end Invalid

/-- Check the same original initial code and every exact saved transition before containment. -/
def prepare {Request : Type u} {Code : Type v} {preparedCode : Code → Prop}
    {preparedStep : Code → Step Request Code → Prop} {invalidCode : Code → Type w}
    {invalidStep : Code → Step Request Code → Type x}
    (prepareCode : (code : Code) → Except (invalidCode code) (PLift (preparedCode code)))
    (prepareStep : (earlier : Code) → (step : Step Request Code) →
      Except (invalidStep earlier step) (PLift (preparedStep earlier step)))
    (history : History Request Code) :
    Except (Invalid invalidCode invalidStep history) (PLift (Valid preparedCode preparedStep history)) :=
  match prepareCode history.initial with
  | .error reason => .error (.initial reason)
  | .ok initial =>
      match Chain.check prepareStep history.initial history.steps with
      | .error reason => .error (.chain reason)
      | .ok chain => .ok ⟨⟨initial.down, chain.down⟩⟩

/-- Read all original saved codes, including the initial code, in chronological order. -/
@[expose] def codes {Request : Type u} {Code : Type v} (history : History Request Code) : List Code :=
  history.initial :: history.steps.map Step.next

/-- Read the saved numerical trace from its original request path and complete cached replies.

Each exchange uses the supplied projection of its stored next code. Its
question retains the actual preceding path; recursion appends that exact
saved request, preserving order and repeated occurrences.
-/
@[expose] def traceFrom {Request : Type u} {Code : Type v} {Reply : Type w}
    (reply : Code → Reply) :
    List Request → List (Step Request Code) → Basic.Trace (Path.Question Request) Reply
  | _, [] => []
  | path, step :: remaining =>
      ⟨⟨path, step.request⟩, reply step.next⟩ :: traceFrom reply (path ++ [step.request]) remaining

namespace State

set_option genInjectivity false in
/-- Matching a request selects its exact saved step and suffix, or leaves the saved path permanently.

A saved selection carries the original remaining-list equality and matching
request equality. Fresh continuation starts from the actual current code.
-/
inductive Selection {Request : Type u} {Code : Type v} {validCode : Code → Prop}
    {validStep : Code → Step Request Code → Prop} (state : State validCode validStep) (request : Request) where
  /-- No saved step is consumed; continuation uses the actual current code. -/ | fresh
  /-- The matching request consumes this same original step and remaining suffix. -/ | saved
      (step : Step Request Code) (remaining : List (Step Request Code))
      (remainingEq : state.remaining = step :: remaining) (same : request = step.request)

/-- Select the same original saved transition only while its actual next request matches.

An empty saved path and the first divergent request select fresh continuation.
The matching branch retains the original step and exact suffix equality.
-/
@[expose] def select {Request : Type u} [DecidableEq Request] {Code : Type v}
    {validCode : Code → Prop} {validStep : Code → Step Request Code → Prop}
    (state : State validCode validStep) (request : Request) : Selection state request :=
  match saved : state.remaining with
  | [] => .fresh
  | step :: remaining =>
      if same : request = step.request then .saved step remaining saved same else .fresh

/-- Answer the original full request path from the same retained history state. -/
@[expose] def answer {Request : Type u} {Code : Type v} {Reply : Type w}
    {validCode : Code → Prop} {validStep : Code → Step Request Code → Prop}
    (step : State validCode validStep → Request → State validCode validStep) (reply : Code → Reply)
    (state : State validCode validStep) (question : Path.Question Request) : Reply :=
  reply (execute step state question.path).code

/-- Saved replay reproduces every complete original reply after its actual preceding path.

The matching-step law consumes the exact retained next code and suffix.
One shared chronological induction establishes every saved occurrence,
including repeated requests and replies.
-/
theorem answers_from {Request : Type u} {Code : Type v} {Reply : Type w}
    {validCode : Code → Prop} {validStep : Code → Step Request Code → Prop}
    (nextValid : ∀ earlier saved, validStep earlier saved → validCode saved.next)
    (step : State validCode validStep → Request → State validCode validStep) (reply : Code → Reply)
    (savedStep : ∀ code valid saved remaining (chain : Chain validStep code (saved :: remaining)),
      step (State.mk code valid (saved :: remaining) chain) saved.request =
        State.mk saved.next (nextValid code saved chain.head) remaining chain.tail)
    (start : State validCode validStep) (path : List Request) (code : Code) (valid : validCode code)
    (saved : List (Step Request Code)) (chain : Chain validStep code saved)
    (reached : execute step start path = State.mk code valid saved chain) :
    Basic.Answers (answer step reply start) (traceFrom reply path saved) := by
  induction chain generalizing path with
  | nil code => intro entry member; nomatch member
  | cons saved head tail induction =>
      have nextReached : execute step start (path ++ [saved.request]) =
          State.mk saved.next (nextValid _ saved head) _ tail := by
        rewrite [execute_append]
        change step (execute step start path) saved.request = _
        rewrite [reached]
        exact savedStep _ _ _ _ _
      intro entry member
      cases List.Membership.mem_cons.mp member with
      | inl same =>
          cases same
          exact congrArg (fun state : State validCode validStep => reply state.code) nextReached
      | inr later => exact induction (path ++ [saved.request]) (nextValid _ saved head) nextReached entry later

end State

set_option genInjectivity false in
/-- A finite containment attempt retains all rejected original codes and the exact inspected budget.

Every saved code is checked using the supplied containment decision. The cached
filter preserves order and repetitions; the budget records one supplied
compatible assignment and every inspected original numerical ball.
-/
structure Attempt {Request : Type u} {Code : Type v}
    (isPrepared : History Request Code → Prop) (contains : Code → Prop)
    [decision : DecidablePred contains] (history : History Request Code) where
  /-- The original history passed its independent checks. -/ prepared : isPrepared history
  /-- Every original code whose supplied candidate fails containment. -/ unresolved : List Code
  /-- The cache is the original filter, preserving order and repetitions. -/ unresolvedEq :
    unresolved = history.codes.filter (fun code => decide (¬ contains code))
  /-- The original code which stopped this finite assignment attempt. -/ rejected : Code
  /-- The rejected code occurs in the original chronological history. -/ member : rejected ∈ history.codes
  /-- The same supplied candidate fails this exact original code's containment. -/ outside : ¬ contains rejected
  /-- The actual number of inspected retained codes. -/ inspected : Nat
  /-- The unresolved filter inspected every original saved code. -/ inspectedEq : inspected = history.codes.length
  /-- The attempted compatible assignment budget. -/ candidateBudget : Nat
  /-- Exactly one supplied assignment was attempted. -/ budgetEq : candidateBudget = 1

namespace Attempt

/-- The cached unresolved list contains exactly the failed original containment occurrences. -/
theorem unresolved_iff {Request : Type u} {Code : Type v}
    {prepared : History Request Code → Prop} {contains : Code → Prop}
    [decision : DecidablePred contains] {history : History Request Code}
    (attempt : Attempt prepared contains history) (code : Code) :
    code ∈ attempt.unresolved ↔ code ∈ history.codes ∧ ¬ contains code := by
  rewrite [attempt.unresolvedEq]
  constructor
  · intro member
    have retained := List.Filter.mem_filter.mp member
    exact ⟨retained.1, of_decide_eq_true retained.2⟩
  · intro failed
    exact List.Filter.mem_filter.mpr ⟨failed.1, decide_eq_true failed.2⟩

end Attempt

set_option genInjectivity false in
/-- History checking retains validity, an identified independent defect or a complete finite containment attempt.

Success certifies the exact supplied history. Independent invalidity and failed
candidate containment remain distinct, with their original typed evidence.
-/
inductive CheckResult {Request : Type u} {Code : Type v} (validHistory : History Request Code → Prop)
    (invalidHistory : History Request Code → Type w) (attemptHistory : History Request Code → Type x)
    (history : History Request Code) where
  /-- This exact supplied history has its complete validity certificate. -/ | valid (certificate : validHistory history)
  /-- The original history has this identified and refuted data defect. -/ | invalid (reason : invalidHistory history)
  /-- The finite containment attempt retains every unresolved code and its budget. -/ | inconclusive
      (attempt : attemptHistory history)

/-- Check the original finite history and supplied candidates without replacing any saved code or cache.

Preparation completes before candidate containment is checked. Success uses
the supplied completion law; failed containment retains the original rejected
code and complete ordered filter of unresolved codes, with the inspected
length and single-candidate budget.
-/
def check {Request : Type u} {Code : Type v} {valid prepared : History Request Code → Prop}
    {invalid : History Request Code → Type w} (contains : Code → Prop) [DecidablePred contains]
    (prepare : (history : History Request Code) → Except (invalid history) (PLift (prepared history)))
    (complete : ∀ history, prepared history → (∀ code ∈ history.codes, contains code) → valid history)
    (history : History Request Code) : CheckResult valid invalid (Attempt prepared contains) history :=
  match prepare history with
  | .error reason => .invalid reason
  | .ok prepared =>
      match List.All.check contains (fun _ => inferInstance) history.codes with
      | .accepted inside => .valid (complete history prepared.down inside)
      | .rejected code member outside => .inconclusive
          ⟨prepared.down, history.codes.filter (fun code => decide (¬ contains code)), rfl,
            code, member, outside, history.codes.length, rfl, 1, rfl⟩

namespace CheckResult

/-- Read whether checking established complete validity of this exact supplied history. -/
@[expose] def succeeded {Request : Type u} {Code : Type v} {valid : History Request Code → Prop}
    {invalid : History Request Code → Type w} {attempt : History Request Code → Type x}
    {history : History Request Code} : CheckResult valid invalid attempt history → Prop
  | .valid _ => True
  | .invalid _ => False
  | .inconclusive _ => False

end CheckResult

/-- A valid original history succeeds in checking with its same compatible supplied candidates. -/
theorem check_of_valid {Request : Type u} {Code : Type v} {valid prepared : History Request Code → Prop}
    {invalid : History Request Code → Type w} (contains : Code → Prop) [DecidablePred contains]
    (prepare : (history : History Request Code) → Except (invalid history) (PLift (prepared history)))
    (complete : ∀ history, prepared history → (∀ code ∈ history.codes, contains code) → valid history)
    (ofValid : ∀ history, valid history → prepared history)
    (refutes : ∀ history, invalid history → ¬ prepared history)
    (all : ∀ history, valid history → ∀ code ∈ history.codes, contains code)
    {history : History Request Code} (certificate : valid history) :
    (check contains prepare complete history).succeeded := by
  cases result : check contains prepare complete history with
  | valid certificate => exact True.intro
  | invalid reason => exact (refutes history reason (ofValid history certificate)).elim
  | inconclusive attempt =>
      exact (attempt.outside (all history certificate attempt.rejected attempt.member)).elim

set_option genInjectivity false in
/-- A trace defect retains the original occurrence whose complete saved reply disagrees with its interpreter. -/
structure TraceInvalid {Question : Type u} {Reply : Type v} (oracle : Question → Reply)
    (trace : Basic.Trace Question Reply) where
  /-- The same original exchange causing this disagreement. -/ entry : Basic.Exchange Question Reply
  /-- The exchange occurs in the original supplied trace. -/ member : entry ∈ trace
  /-- Its complete reply differs from the interpreter at this exact question. -/
  failed : oracle entry.query ≠ entry.reply

namespace TraceInvalid

/-- The identified original reply disagreement refutes interpretation of the same supplied trace. -/
theorem refutes {Question : Type u} {Reply : Type v} {oracle : Question → Reply}
    {trace : Basic.Trace Question Reply} (invalid : TraceInvalid oracle trace) : ¬ Basic.Answers oracle trace :=
  fun answers => invalid.failed (answers invalid.entry invalid.member)

end TraceInvalid

/-- Check complete supplied replies, including repeated questions, against the same retained interpreter.

Equality compares the entire saved reply at each original question. Checking
stops at the first differing occurrence and retains that exchange and its
membership evidence, refuting agreement on the supplied trace.
-/
def validateTrace {Question : Type u} {Reply : Type v} [DecidableEq Reply]
    (oracle : Question → Reply) (trace : Basic.Trace Question Reply) :
    Except (TraceInvalid oracle trace) (PLift (Basic.Answers oracle trace)) :=
  match List.All.check (fun entry : Basic.Exchange Question Reply => oracle entry.query = entry.reply)
      (fun _ => inferInstance) trace with
  | .accepted answers => .ok ⟨answers⟩
  | .rejected entry member failed => .error ⟨entry, member, failed⟩

/-- An interpreter answering every original occurrence passes exact complete-reply trace checking. -/
theorem validateTrace_of_answers {Question : Type u} {Reply : Type v} [DecidableEq Reply]
    (oracle : Question → Reply) (trace : Basic.Trace Question Reply) (answers : Basic.Answers oracle trace) :
    ∃ certificate, validateTrace oracle trace = .ok certificate := by
  cases checked : validateTrace oracle trace with
  | ok certificate => exact ⟨certificate, rfl⟩
  | error invalid => exact (invalid.refutes answers).elim

end History

end Purelib.Computation.Query

end
