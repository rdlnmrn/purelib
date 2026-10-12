module
import Purelib.Data.List.Prefix.Take

-- The exposed advance retains the original concatenation certificate.
public import Purelib.Data.List.Append
public import Purelib.Data.List.BinaryPrefix.Basic
import Mathlib.Data.Nat.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix.Basic renaming SourceEncodingTransducerWordAlias -> Word

section
public section

/-!
# Coherent finite prefix and terminal transducers

The terminating rational CCL encoder already computes a complete finite raw
word.  This module presents that word incrementally: every request appends a
finite segment to the previously emitted prefix, never retracts a bit, and
reaches a certified terminal state after the finite pending suffix is
exhausted.  The construction is structural on explicit lists and does not
parse arbitrary external prefixes.
-/

namespace Purelib.Data.List.Prefix.Cursor

open Purelib.Data

set_option genInjectivity false in
/-- Retain a cursor splitting one fixed finite Boolean word into emitted and pending
parts.

The equality field ties their concatenation to the original complete word. Advancing
the cursor transfers entries from the retained pending suffix to the emitted prefix. -/
structure PrefixState (complete : Word) where
  /-- The prefix already emitted from the retained complete word. -/ emitted : Word
  /-- The exact remaining suffix awaiting later requests. -/ pending : Word
  /-- The complete word is the emitted prefix followed by the pending suffix. -/ complete_eq : complete = emitted ++
    pending

constructive_injectivity PrefixState

namespace PrefixState

section
open Purelib.Data.List.Prefix.Cursor
/-- Initialize a finite-word cursor with no emitted bits and the entire word pending. -/
@[expose] def initial (complete : Word) : PrefixState complete :=
  { emitted := []
    pending := complete
    complete_eq := rfl }

/-- A finite-word cursor is terminal when its retained pending suffix is empty. -/
@[expose] def IsTerminal {complete : Word} (state : PrefixState
  complete) : Prop :=
  state.pending = []

/-- Move at most the requested number of pending bits into the emitted prefix.

Append the pending take to the prior emitted word and retain the pending drop. The
original complete-word equality is preserved by the take/drop decomposition. -/
@[expose] def advance {complete : Word} (state : PrefixState
  complete) (count : Nat) :
    PrefixState complete :=
  { emitted := state.emitted ++ state.pending.take count
    pending := state.pending.drop count
    complete_eq := by
      calc
        complete = state.emitted ++ state.pending := state.complete_eq
        _ = state.emitted ++
            (state.pending.take count ++ state.pending.drop count) := by
          rw [List.take_append_drop]
        _ = (state.emitted ++ state.pending.take count) ++
            state.pending.drop count := (List.Append.append_assoc _ _ _).symm }

/-- The emitted part of a coherent finite-word cursor is a prefix of its original
complete word. -/
theorem emitted_isPrefix {complete : Word} (state : PrefixState
  complete) :
    state.emitted.IsPrefix complete :=
  ⟨state.pending, state.complete_eq.symm⟩

/-- An advance appends exactly the requested take of the prior pending suffix. -/
theorem advance_emitted {complete : Word} (state : PrefixState
  complete)
    (count : Nat) :
    (state.advance count).emitted =
      state.emitted ++ state.pending.take count := rfl

/-- Every advance retains the prior emitted prefix with an explicit appended segment. -/
theorem advance_extends {complete : Word} (state : PrefixState
  complete)
    (count : Nat) :
    ∃ extension : Word,
      (state.advance count).emitted = state.emitted ++ extension :=
  ⟨state.pending.take count, rfl⟩

/-- The emitted length grows by the minimum of the request and the prior pending length. -/
theorem advance_emitted_length {complete : Word}
    (state : PrefixState complete) (count : Nat) :
    (state.advance count).emitted.length =
      state.emitted.length + min count state.pending.length := by
  simp only [-eq_self, -iff_self, advance, List.Append.length_append, List.Prefix.Take.length_take]
  rfl

/-- An advance subtracts the requested count from the pending length, truncated at zero. -/
theorem advance_pending_length {complete : Word}
    (state : PrefixState complete) (count : Nat) :
    (state.advance count).pending.length =
      state.pending.length - count := by
  simp only [-eq_self, -iff_self, advance, List.length_drop]
  rfl

/-- An advance either emits the full requested count or exhausts the pending word.

When the request fits, the exact length equation gives full progress. A larger
request drops the entire pending suffix and yields a terminal state. -/
theorem advance_progress_or_terminal
    {complete : Word} (state : PrefixState complete) (count : Nat) :
    (state.advance count).emitted.length =
        state.emitted.length + count ∨
      (state.advance count).IsTerminal := by
  by_cases within : count ≤ state.pending.length
  · left
    rw [state.advance_emitted_length, Nat.min_eq_left within]
  · right
    unfold IsTerminal advance
    apply List.Prefix.Take.drop_eq_nil_of_le
    exact Nat.le_of_lt (Nat.lt_of_not_ge within)

/-- At a terminal cursor, the emitted prefix equals the retained complete word. -/
theorem emitted_eq_complete_of_terminal
    {complete : Word} (state : PrefixState complete)
    (terminal : state.IsTerminal) :
    state.emitted = complete := by
  have completeIdentity := state.complete_eq
  rw [terminal, List.Append.append_nil] at completeIdentity
  exact completeIdentity.symm

/-- Requesting exactly the pending length makes a finite-word cursor terminal. -/
theorem advance_remaining_terminal
    {complete : Word} (state : PrefixState complete) :
    (state.advance state.pending.length).IsTerminal := by
  unfold IsTerminal advance
  exact List.Prefix.Take.drop_eq_nil_of_le le_rfl

/-- Two successive advances preserve the prefix emitted after the first request. -/
theorem successive_extends {complete : Word}
    (state : PrefixState complete) (first second : Nat) :
    ∃ extension : Word,
      ((state.advance first).advance second).emitted =
        (state.advance first).emitted ++ extension :=
  (state.advance first).advance_extends second

end

end PrefixState
end Purelib.Data.List.Prefix.Cursor

end
