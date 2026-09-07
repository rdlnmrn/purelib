import CCL.Encoding.RawParser
import Lean.Elab.Tactic.Omega

/-!
# Finite progress inside one raw CCL block

Between two completed decoder blocks, the raw parser can only increase one
unary counter and then read a three-bit sector code.  This module records that
finite-state fact as an explicit decreasing budget.  Given thresholds for the
large-tail and initial-low unary runs, every sufficiently long Boolean input
either reaches the applicable threshold at some prefix or completes another
decoder block.
-/

namespace CCL
namespace RawParser

/-- The current unfinished block has accumulated its applicable unary target.
Initial-high and subsequent-loop blocks use `largeTarget`; the initial-low
block uses `smallTarget`.  A partial sector retains the unary exponent that
preceded its delimiter. -/
def Phase.ReachedThreshold (phase : Phase)
    (largeTarget smallTarget : ℕ) : Prop :=
  match phase with
  | .initial => False
  | .highUnary count => largeTarget ≤ count
  | .lowUnary count => smallTarget ≤ count
  | .loopUnary count => largeTarget ≤ count
  | .sector kind exponent _ =>
      match kind with
      | .initialLow => smallTarget ≤ exponent
      | .initialHigh | .loop => largeTarget ≤ exponent

instance (phase : Phase) (largeTarget smallTarget : ℕ) :
    Decidable (phase.ReachedThreshold largeTarget smallTarget) := by
  cases phase with
  | initial => simp only [Phase.ReachedThreshold]; infer_instance
  | highUnary count => simp only [Phase.ReachedThreshold]; infer_instance
  | lowUnary count => simp only [Phase.ReachedThreshold]; infer_instance
  | loopUnary count => simp only [Phase.ReachedThreshold]; infer_instance
  | sector kind exponent bits =>
      cases kind <;> simp only [Phase.ReachedThreshold] <;> infer_instance

/-- Remaining raw bits before either the applicable unary threshold is met or
the current sector code must complete.  The extra three units on unary phases
pay for the sector code following an early false delimiter. -/
def Phase.progressBudget (phase : Phase)
    (largeTarget smallTarget : ℕ) : ℕ :=
  match phase with
  | .initial => max (largeTarget + 3) (smallTarget + 3) + 1
  | .highUnary count => largeTarget - count + 3
  | .lowUnary count => smallTarget - count + 3
  | .loopUnary count => largeTarget - count + 3
  | .sector _ _ .zero => 3
  | .sector _ _ (.one _) => 2
  | .sector _ _ (.two _ _) => 1

theorem Phase.progressBudget_pos (phase : Phase)
    (largeTarget smallTarget : ℕ) :
    0 < phase.progressBudget largeTarget smallTarget := by
  cases phase with
  | initial => simp [Phase.progressBudget]
  | highUnary count => simp [Phase.progressBudget]
  | lowUnary count => simp [Phase.progressBudget]
  | loopUnary count => simp [Phase.progressBudget]
  | sector kind exponent bits =>
      cases bits <;> simp [Phase.progressBudget]

/-- A raw bit never removes a completed historical block. -/
theorem history_length_le_step (state : State) (bit : Bool) :
    state.history.length ≤ (step state bit).history.length := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial => cases bit <;> simp [step]
  | highUnary count => cases bit <;> simp [step]
  | lowUnary count => cases bit <;> simp [step]
  | loopUnary count => cases bit <;> simp [step]
  | sector kind exponent bits =>
      cases bits with
      | zero => simp [step]
      | one first => simp [step]
      | two first second =>
          simp [step, completeSector]

/-- Folding any finite suffix preserves all already-completed history. -/
theorem history_length_le_foldl (state : State) (bits : Prefix.Word) :
    state.history.length ≤ (bits.foldl step state).history.length := by
  induction bits generalizing state with
  | nil => simp
  | cons bit bits inductionHypothesis =>
      exact (history_length_le_step state bit).trans
        (inductionHypothesis (step state bit))

/-- If a bit did not increase completed-history length, it did not apply a
decoder block and therefore left the decoder matrix unchanged. -/
theorem step_matrix_eq_of_history_length_eq (state : State) (bit : Bool)
    (historyEq :
      (step state bit).history.length = state.history.length) :
    (step state bit).matrix = state.matrix := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial => cases bit <;> rfl
  | highUnary count => cases bit <;> rfl
  | lowUnary count => cases bit <;> rfl
  | loopUnary count => cases bit <;> rfl
  | sector kind exponent bits =>
      cases bits with
      | zero => rfl
      | one first => rfl
      | two first second =>
          simp [step, completeSector] at historyEq

/-- A finite suffix with unchanged completed-history length also leaves the
decoder product unchanged. -/
theorem foldl_matrix_eq_of_history_length_eq (state : State)
    (bits : Prefix.Word)
    (historyEq :
      (bits.foldl step state).history.length = state.history.length) :
    (bits.foldl step state).matrix = state.matrix := by
  induction bits generalizing state with
  | nil => rfl
  | cons bit bits inductionHypothesis =>
      let next := step state bit
      have firstMonotone : state.history.length ≤ next.history.length :=
        history_length_le_step state bit
      have restMonotone : next.history.length ≤
          (bits.foldl step next).history.length :=
        history_length_le_foldl next bits
      change (bits.foldl step next).history.length =
        state.history.length at historyEq
      have firstHistoryEq : next.history.length = state.history.length := by
        omega
      have restHistoryEq :
          (bits.foldl step next).history.length = next.history.length := by
        omega
      calc
        ((bit :: bits).foldl step state).matrix =
            (bits.foldl step next).matrix := rfl
        _ = next.matrix := inductionHypothesis next restHistoryEq
        _ = state.matrix :=
          step_matrix_eq_of_history_length_eq state bit firstHistoryEq

/-- Before the first block, an initial or initial-low phase still has exactly
the identity decoder and empty history. -/
private def InitialOrLowInvariant (state : State) : Prop :=
  (state.phase = .initial ∨
    (∃ count, state.phase = .lowUnary count) ∨
    ∃ exponent bits, state.phase = .sector .initialLow exponent bits) →
    state.matrix = identityMatrix ∧ state.history = []

private theorem InitialOrLowInvariant.preserved_step {state : State}
    (invariant : InitialOrLowInvariant state) (bit : Bool) :
    InitialOrLowInvariant (RawParser.step state bit) := by
  intro eligible
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      have before := invariant (Or.inl rfl)
      cases bit <;> simpa [RawParser.step] using before
  | highUnary count =>
      cases bit <;> simp [RawParser.step] at eligible
  | lowUnary count =>
      have before := invariant (Or.inr (Or.inl ⟨count, rfl⟩))
      cases bit <;> simpa [RawParser.step] using before
  | loopUnary count =>
      cases bit <;> simp [RawParser.step] at eligible
  | sector kind exponent bits =>
      cases kind with
      | initialLow =>
          have before := invariant
            (Or.inr (Or.inr ⟨exponent, bits, rfl⟩))
          cases bits with
          | zero => simpa [RawParser.step] using before
          | one first => simpa [RawParser.step] using before
          | two first second =>
              simp [RawParser.step, completeSector] at eligible
      | initialHigh =>
          cases bits with
          | zero => simp [RawParser.step] at eligible
          | one first => simp [RawParser.step] at eligible
          | two first second =>
              simp [RawParser.step, completeSector] at eligible
      | loop =>
          cases bits with
          | zero => simp [RawParser.step] at eligible
          | one first => simp [RawParser.step] at eligible
          | two first second =>
              simp [RawParser.step, completeSector] at eligible

private theorem InitialOrLowInvariant.preserved_foldl {state : State}
    (invariant : InitialOrLowInvariant state) (bits : Prefix.Word) :
    InitialOrLowInvariant (bits.foldl RawParser.step state) := by
  induction bits generalizing state with
  | nil => exact invariant
  | cons bit bits inductionHypothesis =>
      exact inductionHypothesis (invariant.preserved_step bit)

/-- The initial-low phase occurs before the first completed block, so its
decoder matrix and retained history are still exactly initial. -/
theorem parse_matrix_history_eq_initial_of_initial_or_low
    (word : Prefix.Word)
    (eligible : (parse word).phase = .initial ∨
      ∃ count, (parse word).phase = .lowUnary count) :
    (parse word).matrix = identityMatrix ∧ (parse word).history = [] := by
  have initialInvariant : InitialOrLowInvariant initialState := by
    intro
    simp [initialState]
  exact (initialInvariant.preserved_foldl word)
    (eligible.imp_right Or.inl)

theorem parse_matrix_eq_identity_of_lowUnary
    {word : Prefix.Word} {count : ℕ}
    (phase : (parse word).phase = .lowUnary count) :
    (parse word).matrix = identityMatrix :=
  (parse_matrix_history_eq_initial_of_initial_or_low word
    (Or.inr ⟨count, phase⟩)).1

theorem parse_history_eq_nil_of_lowUnary
    {word : Prefix.Word} {count : ℕ}
    (phase : (parse word).phase = .lowUnary count) :
    (parse word).history = [] :=
  (parse_matrix_history_eq_initial_of_initial_or_low word
    (Or.inr ⟨count, phase⟩)).2

/-- A partial initial-low sector code likewise precedes the first decoder
update and therefore still uses the identity matrix. -/
theorem parse_matrix_eq_identity_of_initialLow_sector
    {word : Prefix.Word} {exponent : ℕ} {bits : SectorBits}
    (phase : (parse word).phase = .sector .initialLow exponent bits) :
    (parse word).matrix = identityMatrix := by
  have initialInvariant : InitialOrLowInvariant initialState := by
    intro
    simp [initialState]
  exact ((initialInvariant.preserved_foldl word)
    (Or.inr (Or.inr ⟨exponent, bits, phase⟩))).1

/-- A partial initial-low sector code has not completed its first decoder
block, so its retained history is still empty. -/
theorem parse_history_eq_nil_of_initialLow_sector
    {word : Prefix.Word} {exponent : ℕ} {bits : SectorBits}
    (phase : (parse word).phase = .sector .initialLow exponent bits) :
    (parse word).history = [] := by
  have initialInvariant : InitialOrLowInvariant initialState := by
    intro
    simp [initialState]
  exact ((initialInvariant.preserved_foldl word)
    (Or.inr (Or.inr ⟨exponent, bits, phase⟩))).2

/-- Unless the current phase has already reached its unary target, every bit
that does not complete a block strictly reduces the finite progress budget. -/
theorem progressBudget_step_lt
    (state : State) (bit : Bool) (largeTarget smallTarget : ℕ)
    (notReached :
      ¬state.phase.ReachedThreshold largeTarget smallTarget)
    (historyUnchanged :
      (step state bit).history.length = state.history.length) :
    (step state bit).phase.progressBudget largeTarget smallTarget <
      state.phase.progressBudget largeTarget smallTarget := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;> simp [step, Phase.progressBudget] <;> omega
  | highUnary count =>
      cases bit <;>
        simp [step, Phase.ReachedThreshold, Phase.progressBudget]
          at notReached ⊢ <;> omega
  | lowUnary count =>
      cases bit <;>
        simp [step, Phase.ReachedThreshold, Phase.progressBudget]
          at notReached ⊢ <;> omega
  | loopUnary count =>
      cases bit <;>
        simp [step, Phase.ReachedThreshold, Phase.progressBudget]
          at notReached ⊢ <;> omega
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp [step, Phase.progressBudget]
      | one first =>
          simp [step, Phase.progressBudget]
      | two first second =>
          simp [step, completeSector] at historyUnchanged

/-- Some prefix of `bits` reaches an applicable unary threshold. -/
def ReachesThresholdWithin (state : State) (bits : Prefix.Word)
    (largeTarget smallTarget : ℕ) : Prop :=
  ∃ consumed remaining : Prefix.Word,
    bits = consumed ++ remaining ∧
      ((consumed.foldl step state).phase.ReachedThreshold
        largeTarget smallTarget) ∧
      (consumed.foldl step state).history.length = state.history.length

/-- Data-bearing form of local parser progress.  Unlike a proposition-only
existential, the consumed prefix remains available to executable callers. -/
inductive ThresholdOrHistoryResult (state : State) (bits : Prefix.Word)
    (largeTarget smallTarget : ℕ) where
  | threshold (consumed remaining : Prefix.Word)
      (bits_eq : bits = consumed ++ remaining)
      (reached : (consumed.foldl step state).phase.ReachedThreshold
        largeTarget smallTarget)
      (history_eq :
        (consumed.foldl step state).history.length = state.history.length)
  | historyGrew
      (grew : state.history.length <
        (bits.foldl step state).history.length)

/-- Execute the finite progress scan certified by `progressBudget`. -/
def thresholdOrHistory
    (state : State) (bits : Prefix.Word) (largeTarget smallTarget : ℕ)
    (enough :
      state.phase.progressBudget largeTarget smallTarget ≤ bits.length) :
    ThresholdOrHistoryResult state bits largeTarget smallTarget := by
  by_cases reached :
      state.phase.ReachedThreshold largeTarget smallTarget
  · exact .threshold [] bits (by simp) (by simpa using reached) rfl
  · cases bits with
    | nil =>
        have positive := state.phase.progressBudget_pos
          largeTarget smallTarget
        simp only [List.length_nil] at enough
        omega
    | cons bit rest =>
        let next := step state bit
        have historyMonotone :
            state.history.length ≤ next.history.length := by
          exact history_length_le_step state bit
        by_cases historyGrew : state.history.length < next.history.length
        · exact .historyGrew (historyGrew.trans_le
            (history_length_le_foldl next rest))
        · have historyEq : next.history.length = state.history.length := by
            omega
          have budgetDrops :
              next.phase.progressBudget largeTarget smallTarget <
                state.phase.progressBudget largeTarget smallTarget := by
            exact progressBudget_step_lt state bit largeTarget smallTarget
              reached historyEq
          have enoughRest :
              next.phase.progressBudget largeTarget smallTarget ≤ rest.length := by
            simp only [List.length_cons] at enough
            omega
          match thresholdOrHistory next rest largeTarget smallTarget
              enoughRest with
          | .threshold consumed remaining wordEq atThreshold consumedHistory =>
              exact .threshold (bit :: consumed) remaining
                (by simp [wordEq])
                (by simpa only [List.foldl_cons] using atThreshold)
                (by
                  simpa only [List.foldl_cons, next, historyEq] using
                    consumedHistory)
          | .historyGrew grew =>
              exact .historyGrew (by
                change state.history.length <
                  (rest.foldl step (step state bit)).history.length
                rw [← historyEq]
                simpa only [next] using grew)
termination_by bits.length

/-- Constructive local block progress.  Once the explicit phase budget fits
inside the supplied finite input, either a displayed prefix reaches the unary
threshold or the whole input has completed at least one additional decoder
block. -/
theorem reachesThresholdWithin_or_history_grows
    (state : State) (bits : Prefix.Word) (largeTarget smallTarget : ℕ)
    (enough :
      state.phase.progressBudget largeTarget smallTarget ≤ bits.length) :
    ReachesThresholdWithin state bits largeTarget smallTarget ∨
      state.history.length < (bits.foldl step state).history.length := by
  by_cases reached :
      state.phase.ReachedThreshold largeTarget smallTarget
  · exact Or.inl ⟨[], bits, by simp, by simpa using reached, rfl⟩
  · cases bits with
    | nil =>
        have positive := state.phase.progressBudget_pos
          largeTarget smallTarget
        simp only [List.length_nil] at enough
        omega
    | cons bit rest =>
        let next := step state bit
        have historyMonotone :
            state.history.length ≤ next.history.length := by
          exact history_length_le_step state bit
        by_cases historyGrew : state.history.length < next.history.length
        · exact Or.inr (historyGrew.trans_le
            (history_length_le_foldl next rest))
        · have historyEq : next.history.length = state.history.length := by
            omega
          have budgetDrops :
              next.phase.progressBudget largeTarget smallTarget <
                state.phase.progressBudget largeTarget smallTarget := by
            exact progressBudget_step_lt state bit largeTarget smallTarget
              reached historyEq
          have enoughRest :
              next.phase.progressBudget largeTarget smallTarget ≤ rest.length := by
            simp only [List.length_cons] at enough
            omega
          have progress := reachesThresholdWithin_or_history_grows
            next rest largeTarget smallTarget enoughRest
          cases progress with
          | inl within =>
              rcases within with
                ⟨consumed, remaining, wordEq, atThreshold, consumedHistory⟩
              exact Or.inl
                ⟨bit :: consumed, remaining, by simp [wordEq], by
                  simpa only [List.foldl_cons] using atThreshold, by
                  simpa only [List.foldl_cons, next, historyEq] using
                    consumedHistory⟩
          | inr grew =>
              exact Or.inr (by
                change state.history.length <
                  (rest.foldl step (step state bit)).history.length
                rw [← historyEq]
                simpa only [next] using grew)
termination_by bits.length

end RawParser
end CCL
