import CCL.Riemann.LegendrePositivityAcquisition

/-!
# Finite regression clients for discovered Legendre positivity

The delayed imaginary unit first exhausts a budget, then succeeds from the
retained state. The exact zero client stays unresolved at every finite budget.
These exercise both outcomes without evaluating a large generated period bank.
-/

namespace CCL.Riemann.LegendrePositivityAcquisitionExamples

open CCL.Riemann.LegendrePositivityAcquisition

abbrev Process := CCL.ProgressiveEnclosures.Process
abbrev Coherent := CCL.ProgressiveCoherence.Coherent

def imaginaryUnit : Gaussian := ⟨0, 1⟩

def delayedProcess : Process where
  State := Bool
  ball state := if state then
    { center := imaginaryUnit, radiusSq := 0, radiusSq_nonneg := le_rfl }
    else { center := 0, radiusSq := 4, radiusSq_nonneg := by decide }
  Possible _ value := value = imaginaryUnit
  witness _ := ⟨imaginaryUnit, rfl⟩
  possible_inside := by
    intro state value equal
    subst value
    cases state <;> decide
  refine _ _ _ := true
  refine_persists := by
    intro state target positive value possible
    exact possible
  accurate := by
    intro state target positive
    exact positive
  centerBound := 1
  centerBound_nonneg := by decide
  center_bounded := by
    intro state
    cases state <;> decide

def delayedAllowance (state : Bool) : Q := if state then 0 else 4

def delayedCoherent : Coherent delayedProcess where
  allowance := delayedAllowance
  allowance_nonneg := by intro state; cases state <;> decide
  ball_radius_le := by intro state; cases state <;> decide
  possible_close := by
    intro left right leftValue rightValue leftEqual rightEqual
    subst leftValue
    subst rightValue
    cases left <;> cases right <;> decide
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    exact positive

def delayed : CoherentNamed where
  name := { process := delayedProcess, state := false }
  coherent := delayedCoherent

theorem initial_unresolved : ¬ PositiveTest (initial delayed).ball := by decide

theorem refined_positive : PositiveTest (advance (initial delayed)).ball := by decide

/-- One unit of work retains its genuine refinement on exhaustion. -/
theorem one_unit_exhausts :
    attempt delayed (initial delayed) 1 = .exhausted (advance (initial delayed)) := by
  rw [attempt_succ_of_unresolved (initial delayed) initial_unresolved 0]
  rfl

/-- The retained state succeeds with one further inspection, without a
caller-supplied enclosure or denominator preparation. -/
theorem resumed_succeeds :
    attempt delayed (advance (initial delayed)) 1 =
      .ready (enclosure (advance (initial delayed)) refined_positive) :=
  attempt_one_of_positive _ refined_positive

theorem two_units_succeed :
    attempt delayed (initial delayed) 2 =
      .ready (enclosure (advance (initial delayed)) refined_positive) := by
  rw [attempt_succ_of_unresolved (initial delayed) initial_unresolved 1]
  exact resumed_succeeds

/-- Automatic discovery feeds the certified evaluator for any displayed
finite word; this example supplies no per-word certificates. -/
theorem discovered_word_ready (word : Word) :
    attemptTransport delayed word (initial delayed) 2 =
      .ready (CCL.Riemann.LegendreAutomaticTransport.guaranteed
        (enclosure (advance (initial delayed)) refined_positive) word) := by
  unfold attemptTransport
  rw [two_units_succeed]

/-- The same discovery prepares every intermediate division as well. -/
theorem discovered_fold_ready (word : Word) :
    attemptFold delayed word (initial delayed) 2 =
      .ready (CCL.Riemann.LegendreGuaranteedFold.prepareWord
        (enclosure (advance (initial delayed)) refined_positive) word) := by
  unfold attemptFold
  rw [two_units_succeed]

def zeroInput : CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed.exact 0

theorem zero_unresolved (state : State zeroInput) : ¬ PositiveTest state.ball := by
  rw [state.ball_eq]
  intro test
  exact (lt_irrefl (0 : Q)) test.1

/-- No finite amount of work invents positivity for the exact zero input.
The result is exhaustion, preserving the finite refinement state. -/
theorem zero_exhausts (state : State zeroInput) (fuel : Nat) :
    attempt zeroInput state fuel = .exhausted (advanceN state fuel) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      rw [attempt_succ_of_unresolved state (zero_unresolved state) fuel]
      exact inductionHypothesis (advance state)

end CCL.Riemann.LegendrePositivityAcquisitionExamples
