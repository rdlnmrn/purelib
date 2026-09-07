import CCL.Encoding.Encoder

/-!
# Coherent finite prefix and terminal transducers

The terminating rational CCL encoder already computes a complete finite raw
word.  This module presents that word incrementally: every request appends a
finite segment to the previously emitted prefix, never retracts a bit, and
reaches a certified terminal state after the finite pending suffix is
exhausted.  The construction is structural on explicit lists and does not
parse arbitrary external prefixes.
-/

namespace CCL.Transducer

abbrev Word := List Bool
abbrev Frac := CCL.Integral.Frac
abbrev BlockEncoding := CCL.Encoder.BlockEncoding

open CCL.Cylinder

/-- A coherent cursor through one fixed complete finite raw word. -/
structure PrefixState (complete : Word) where
  emitted : Word
  pending : Word
  complete_eq : complete = emitted ++ pending

namespace PrefixState

def initial (complete : Word) : PrefixState complete :=
  { emitted := []
    pending := complete
    complete_eq := by simp }

def IsTerminal {complete : Word} (state : PrefixState complete) : Prop :=
  state.pending = []

/-- Emit at most `count` further bits from the explicit pending suffix. -/
def advance {complete : Word} (state : PrefixState complete) (count : Nat) :
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
            state.pending.drop count := (List.append_assoc _ _ _).symm }

/-- Every emitted state is a prefix of the same complete word. -/
theorem emitted_isPrefix {complete : Word} (state : PrefixState complete) :
    state.emitted.IsPrefix complete :=
  ⟨state.pending, state.complete_eq.symm⟩

/-- One request extends the prior prefix by exactly the finite segment it
takes from the pending suffix. -/
theorem advance_emitted {complete : Word} (state : PrefixState complete)
    (count : Nat) :
    (state.advance count).emitted =
      state.emitted ++ state.pending.take count := rfl

theorem advance_extends {complete : Word} (state : PrefixState complete)
    (count : Nat) :
    ∃ extension : Word,
      (state.advance count).emitted = state.emitted ++ extension :=
  ⟨state.pending.take count, rfl⟩

/-- Exact finite progress: the emitted length grows by the smaller of the
request and the number of remaining bits. -/
theorem advance_emitted_length {complete : Word}
    (state : PrefixState complete) (count : Nat) :
    (state.advance count).emitted.length =
      state.emitted.length + min count state.pending.length := by
  simp only [advance, List.length_append, List.length_take]

theorem advance_pending_length {complete : Word}
    (state : PrefixState complete) (count : Nat) :
    (state.advance count).pending.length =
      state.pending.length - count := by
  simp only [advance, List.length_drop]

/-- A request either emits exactly the requested number of additional bits,
or exhausts the finite word and reaches the terminal state. -/
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
    apply List.drop_eq_nil_of_le
    exact Nat.le_of_lt (Nat.lt_of_not_ge within)

/-- Once terminal, the emitted prefix is the complete encoded word. -/
theorem emitted_eq_complete_of_terminal
    {complete : Word} (state : PrefixState complete)
    (terminal : state.IsTerminal) :
    state.emitted = complete := by
  have completeIdentity := state.complete_eq
  rw [terminal, List.append_nil] at completeIdentity
  exact completeIdentity.symm

/-- Asking for all remaining bits reaches the terminal state. -/
theorem advance_remaining_terminal
    {complete : Word} (state : PrefixState complete) :
    (state.advance state.pending.length).IsTerminal := by
  unfold IsTerminal advance
  exact List.drop_eq_nil_of_le le_rfl

/-- Successive calls are coherent by construction: the later state extends
the prefix returned by the immediately preceding call. -/
theorem successive_extends {complete : Word}
    (state : PrefixState complete) (first second : Nat) :
    ∃ extension : Word,
      ((state.advance first).advance second).emitted =
        (state.advance first).emitted ++ extension :=
  (state.advance first).advance_extends second

end PrefixState

/-- Incremental view of one exact completed-block encoding. -/
structure EncodingTransducer (fraction : Frac) where
  encoding : BlockEncoding fraction
  state : PrefixState (rawWord encoding.blocks)

namespace EncodingTransducer

def initial {fraction : Frac} (encoding : BlockEncoding fraction) :
    EncodingTransducer fraction :=
  { encoding := encoding
    state := PrefixState.initial (rawWord encoding.blocks) }

def advance {fraction : Frac} (transducer : EncodingTransducer fraction)
    (count : Nat) : EncodingTransducer fraction :=
  { encoding := transducer.encoding
    state := transducer.state.advance count }

def IsTerminal {fraction : Frac}
    (transducer : EncodingTransducer fraction) : Prop :=
  transducer.state.IsTerminal

theorem emitted_isPrefix {fraction : Frac}
    (transducer : EncodingTransducer fraction) :
    transducer.state.emitted.IsPrefix
      (rawWord transducer.encoding.blocks) :=
  transducer.state.emitted_isPrefix

theorem advance_extends {fraction : Frac}
    (transducer : EncodingTransducer fraction) (count : Nat) :
    ∃ extension : Word,
      (transducer.advance count).state.emitted =
        transducer.state.emitted ++ extension :=
  transducer.state.advance_extends count

theorem advance_remaining_terminal {fraction : Frac}
    (transducer : EncodingTransducer fraction) :
    (transducer.advance transducer.state.pending.length).IsTerminal :=
  transducer.state.advance_remaining_terminal

theorem advance_progress_or_terminal {fraction : Frac}
    (transducer : EncodingTransducer fraction) (count : Nat) :
    (transducer.advance count).state.emitted.length =
        transducer.state.emitted.length + count ∨
      (transducer.advance count).IsTerminal :=
  transducer.state.advance_progress_or_terminal count

/-- A terminal incremental state has emitted the exact complete word and its
stored completed-block realization reconstructs the encoded rational value. -/
theorem terminal_spec {fraction : Frac}
    (transducer : EncodingTransducer fraction)
    (terminal : transducer.IsTerminal) :
    transducer.state.emitted = rawWord transducer.encoding.blocks ∧
      transducer.encoding.point.Equivalent
        (CCL.Proj.affine fraction.value) :=
  ⟨transducer.state.emitted_eq_complete_of_terminal terminal,
    transducer.encoding.reconstruct⟩

end EncodingTransducer

/-- Canonical coherent transducer for the terminating rational encoder. -/
def encode (fraction : Frac) (numeratorNonzero : fraction.num ≠ 0) :
    EncodingTransducer fraction :=
  EncodingTransducer.initial
    (CCL.Encoder.encodeBlocks fraction numeratorNonzero)

theorem encode_completeWord
    (fraction : Frac) (numeratorNonzero : fraction.num ≠ 0) :
    rawWord (encode fraction numeratorNonzero).encoding.blocks =
      CCL.Encoder.encode fraction numeratorNonzero :=
  (CCL.Encoder.encode_eq_rawWord fraction numeratorNonzero).symm

theorem encode_advance_extends
    (fraction : Frac) (numeratorNonzero : fraction.num ≠ 0)
    (count : Nat) :
    ∃ extension : Word,
      ((encode fraction numeratorNonzero).advance count).state.emitted =
        (encode fraction numeratorNonzero).state.emitted ++ extension :=
  (encode fraction numeratorNonzero).advance_extends count

theorem encode_reaches_terminal
    (fraction : Frac) (numeratorNonzero : fraction.num ≠ 0) :
    ((encode fraction numeratorNonzero).advance
      (encode fraction numeratorNonzero).state.pending.length).IsTerminal :=
  (encode fraction numeratorNonzero).advance_remaining_terminal

end CCL.Transducer
