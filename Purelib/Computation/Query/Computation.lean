module

import Init.Data.List.Lemmas

-- Exposed protocol constructors retain the exact concatenation and membership certificates.
public import Purelib.Data.List.Append
public import Purelib.Data.List.Membership
public import Purelib.Computation.Query.Basic
public import Purelib.Computation.Query.Replay
import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite adaptive query recording and replay

A computation is built from finite pure work, one displayed query, and
sequential composition.  Its executed log is a finite ordered list, not an
enumeration of all possible replies.  A continuation is an executable
procedure which may select its next query from the reply just received.

The recording and replay laws are proved by the constructors.  In particular,
replay has no oracle argument, and agreement on the first run's requested
replies forces the second run's requests as well as its result.  Concrete
clients must keep their fixed control data separate from the oracle passed to
`run`; arbitrary function parameters alone are not claims of computability.
-/

public section

namespace Purelib.Computation.Query

open Purelib.Computation.Query
open Purelib.Data.List

universe u v w x

set_option genInjectivity false in
/-- An executable finite query protocol with recording and replay laws.

Running records the ordered trace. Replay consumes exactly that trace while preserving any suffix, and agreement on its
replies determines the whole execution. -/
structure Protocol (Query : Type u) (Reply : Type v) (Value : Type w) where
  /-- Run with an oracle and retain the returned value and trace. -/ run : (Query → Reply) → Basic.Execution Query Reply
    Value
  /-- Consume a trace prefix, returning a value and unused suffix or a concrete error. -/ replay : Basic.Trace Query
    Reply → Except (Replay.ReplayError Query) (Value × Basic.Trace Query Reply)
  /-- Replay of a recorded execution returns its value and leaves any appended suffix. -/ replay_run_suffix : ∀ oracle
    suffix,
    replay ((run oracle).trace ++ suffix) = .ok ((run oracle).value, suffix)
  /-- Every recorded reply equals the reply supplied by the running oracle. -/ answers_run : ∀ oracle, Basic.Answers
    oracle (run oracle).trace
  /-- Agreement on the first run's replies determines the complete second execution. -/ run_of_answers : ∀ first second,
    Basic.Answers second (run first).trace → run second = run first

constructive_injectivity Protocol

namespace Protocol.mk

end Protocol.mk

namespace Protocol.mk

end Protocol.mk

namespace Protocol

open _root_.Purelib.Computation.Query renaming Protocol -> Protocol

variable {Query : Type u} {Reply : Type v} {Value : Type w} {Result : Type x}

/-- Return a value without issuing or consuming any queries. -/
@[expose] def pure (value : Value) : Protocol Query Reply Value where
  run _ := ⟨value, []⟩
  replay remaining := .ok (value, remaining)
  replay_run_suffix _ _ := rfl
  answers_run _ _ member := by nomatch member
  run_of_answers _ _ _ := rfl

/-- Issue one query and record its reply.

Replay checks the next recorded query using decidable equality and returns its reply. An empty or mismatched trace
produces the corresponding concrete error. -/
@[expose] def query [DecidableEq Query] (question : Query) : Protocol Query Reply Reply where
  run oracle := ⟨oracle question, [⟨question, oracle question⟩]⟩
  replay
    | [] => .error (.missing question)
    | entry :: rest =>
        if equal : entry.query = question then .ok (entry.reply, rest)
        else .error (.mismatch question entry.query equal)
  replay_run_suffix := by
    intro oracle suffix
    dsimp only [List.cons_append, List.nil_append]
    rw [dif_pos rfl]
  answers_run := by
    intro oracle entry member
    have equal : entry = ⟨question, oracle question⟩ :=
      Membership.mem_singleton.mp member
    exact equal ▸ rfl
  run_of_answers := by
    intro first second agrees
    have replyEqual : second question = first question :=
      agrees ⟨question, first question⟩ (List.Mem.head [])
    change (⟨second question, [⟨question, second question⟩]⟩ : Basic.Execution Query Reply Reply) = _
    rw [replyEqual]

/-- Compose two query computations in execution order.

The first returned value selects the second computation. Their traces are concatenated with order and multiplicity
preserved; replay passes along the unused suffix. -/
@[expose] def bind (first : Protocol Query Reply Value)
    (next : Value → Protocol Query Reply Result) : Protocol Query Reply Result where
  run oracle :=
    let before := first.run oracle
    let after := (next before.value).run oracle
    ⟨after.value, before.trace ++ after.trace⟩
  replay remaining :=
    match first.replay remaining with
    | .error error => .error error
    | .ok (value, rest) => (next value).replay rest
  replay_run_suffix := by
    intro oracle suffix
    rw [Append.append_assoc, first.replay_run_suffix]
    exact (next (first.run oracle).value).replay_run_suffix oracle suffix
  answers_run := by
    intro oracle entry member
    rcases Membership.mem_append.mp member with before | after
    · exact first.answers_run oracle entry before
    · exact (next (first.run oracle).value).answers_run oracle entry after
  run_of_answers := by
    intro left right agrees
    have before : first.run right = first.run left := first.run_of_answers left right
      (fun entry member => agrees entry (Membership.mem_append.mpr (Or.inl member)))
    have after : (next (first.run left).value).run right =
        (next (first.run left).value).run left :=
      (next (first.run left).value).run_of_answers left right
        (fun entry member => agrees entry (Membership.mem_append.mpr (Or.inr member)))
    dsimp only
    rw [before, after]

/-- Transform the returned value while preserving the query trace. -/
@[expose] def map (function : Value → Result) (computation : Protocol Query Reply Value) :
    Protocol Query Reply Result := computation.bind fun value => pure (function value)

/-- A composed run returns the value of its selected second computation. -/
theorem bind_run_value (first : Protocol Query Reply Value)
    (next : Value → Protocol Query Reply Result) (oracle : Query → Reply) :
    ((first.bind next).run oracle).value = ((next (first.run oracle).value).run oracle).value := rfl

/-- A composed run concatenates the first trace and selected second trace. -/
theorem bind_run_trace (first : Protocol Query Reply Value)
    (next : Value → Protocol Query Reply Result) (oracle : Query → Reply) :
    ((first.bind next).run oracle).trace =
      (first.run oracle).trace ++ ((next (first.run oracle).value).run oracle).trace := rfl

/-- Apply a state-dependent query computation a displayed finite number of times.

The next step uses the previous returned state. Recording and replay laws are retained through sequential composition,
including all ordered query occurrences. -/
@[expose] def iterate (step : Value → Protocol Query Reply Value) :
    Nat → Value → Protocol Query Reply Value
  | 0, state => pure state
  | count + 1, state => (step state).bind (iterate step count)

/-- Mapping transforms the returned value by the supplied function. -/
theorem map_run_value (function : Value → Result) (computation : Protocol Query Reply Value)
    (oracle : Query → Reply) :
    ((computation.map function).run oracle).value = function (computation.run oracle).value := rfl

/-- Mapping preserves the complete recorded trace. -/
theorem map_run_trace (function : Value → Result) (computation : Protocol Query Reply Value)
    (oracle : Query → Reply) :
    ((computation.map function).run oracle).trace = (computation.run oracle).trace :=
  Append.append_nil _

/-- Replay a computation and reject any unused recorded queries.

A successful result consumes the entire supplied finite trace. Missing, mismatched and trailing queries remain
distinguishable errors. -/
@[expose] def replayExact (computation : Protocol Query Reply Value) (trace : Basic.Trace Query Reply) :
    Except (Replay.ReplayError Query) Value :=
  match computation.replay trace with
  | .error error => .error error
  | .ok (value, []) => .ok value
  | .ok (_, entry :: _) => .error (.trailing entry.query)

/-- Exact replay accepts a run's trace and returns its recorded value. -/
theorem replayExact_run (computation : Protocol Query Reply Value) (oracle : Query → Reply) :
    computation.replayExact (computation.run oracle).trace = .ok (computation.run oracle).value := by
  unfold replayExact
  have replay := computation.replay_run_suffix oracle []
  rw [Append.append_nil] at replay
  rw [replay]

/-- Agreement on recorded replies forces equality of the complete run traces. -/
theorem trace_eq_of_answers (computation : Protocol Query Reply Value)
    (first second : Query → Reply) (agrees : Basic.Answers second (computation.run first).trace) :
    (computation.run second).trace = (computation.run first).trace :=
  congrArg Basic.Execution.trace (computation.run_of_answers first second agrees)

/-- Agreement on recorded replies forces equality of the returned values. -/
theorem value_eq_of_answers (computation : Protocol Query Reply Value)
    (first second : Query → Reply) (agrees : Basic.Answers second (computation.run first).trace) :
    (computation.run second).value = (computation.run first).value :=
  congrArg Basic.Execution.value (computation.run_of_answers first second agrees)

end Protocol

end Purelib.Computation.Query

end
