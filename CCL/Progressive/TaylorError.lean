import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.HigherJet

/-!
# Finite error transport for progressive Taylor tables

The progressive higher-jet layer emits every displayed coefficient.  This
module transports those finitely many coefficient allowances through Horner
evaluation and through an explicit finite truncation.  The bounds are coarse
recursive rational expressions; no omitted infinite tail or formal power
series is introduced.
-/

namespace CCL.ProgressiveTaylorError

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed

open RFAP.ConstructiveGaussian.Gaussian

/-- Low-to-high Horner evaluation for a displayed finite Gaussian table. -/
def eval : List Gaussian → Gaussian → Gaussian
  | [], _ => 0
  | coefficient :: remaining, input =>
      coefficient + input * eval remaining input

/-- A finite coefficientwise squared-error relation. -/
def EntriesClose : List Gaussian → List Gaussian → Coordinate → Prop
  | [], [], _ => True
  | actual :: actualTail, displayed :: displayedTail, target =>
      normSq (actual - displayed) ≤ target ∧
        EntriesClose actualTail displayedTail target
  | _, _, _ => False

/-- Coarse Horner error budget for `count` coefficients, a common
coefficient allowance, and the displayed input quadrance. -/
def evaluationErrorBudget : Nat → Coordinate → Coordinate → Coordinate
  | 0, _, _ => 0
  | count + 1, coefficientAllowance, inputNormSq =>
      2 * (coefficientAllowance +
        inputNormSq * evaluationErrorBudget count coefficientAllowance
          inputNormSq)

theorem evaluationErrorBudget_nonneg : ∀ count
    {coefficientAllowance inputNormSq : Coordinate},
    0 ≤ coefficientAllowance → 0 ≤ inputNormSq →
      0 ≤ evaluationErrorBudget count coefficientAllowance inputNormSq
  | 0, _coefficientAllowance, _inputNormSq, _coefficientNonnegative,
      _inputNonnegative => le_rfl
  | count + 1, coefficientAllowance, inputNormSq,
      coefficientNonnegative, inputNonnegative =>
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg coefficientNonnegative
          (RFAP.ConstructiveFraction.mul_nonneg_direct inputNonnegative
            (evaluationErrorBudget_nonneg count coefficientNonnegative
              inputNonnegative)))

private theorem eval_difference_cons (actual displayed : Gaussian)
    (actualTail displayedTail : List Gaussian) (input : Gaussian) :
    eval (actual :: actualTail) input -
        eval (displayed :: displayedTail) input =
      (actual - displayed) +
        input * (eval actualTail input - eval displayedTail input) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [eval, sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1

/-- Finite coefficient allowances compute a rational allowance for the
evaluated Taylor table. -/
theorem eval_error_le : ∀ (actual displayed : List Gaussian)
    (input : Gaussian) (coefficientAllowance : Coordinate),
    EntriesClose actual displayed coefficientAllowance →
      normSq (eval actual input - eval displayed input) ≤
        evaluationErrorBudget actual.length coefficientAllowance
          (normSq input)
  | [], [], input, coefficientAllowance, _valid => by
      change normSq ((0 : Gaussian) - 0) ≤ 0
      rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
  | [], _ :: _, input, coefficientAllowance, valid => by
      simp only [EntriesClose] at valid
  | _ :: _, [], input, coefficientAllowance, valid => by
      simp only [EntriesClose] at valid
  | actual :: actualTail, displayed :: displayedTail, input,
      coefficientAllowance, valid => by
      rcases valid with ⟨headClose, tailValid⟩
      rw [eval_difference_cons]
      calc
        normSq
            ((actual - displayed) +
              input * (eval actualTail input - eval displayedTail input)) ≤
          2 * (normSq (actual - displayed) +
            normSq (input *
              (eval actualTail input - eval displayedTail input))) :=
          normSq_add_le_two _ _
        _ = 2 * (normSq (actual - displayed) +
            normSq input *
              normSq (eval actualTail input - eval displayedTail input)) := by
          rw [normSq_mul]
        _ ≤ 2 * (coefficientAllowance +
            normSq input *
              evaluationErrorBudget actualTail.length coefficientAllowance
                (normSq input)) := by
          apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
            (by decide)
          exact add_le_add headClose
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (eval_error_le actualTail displayedTail input
                coefficientAllowance tailValid)
              (normSq_nonneg input))
        _ = evaluationErrorBudget (actual :: actualTail).length
            coefficientAllowance (normSq input) := rfl

/-! ## Connecting shared progressive requests to the finite relation -/

def sharedCenter (budget : List CoherentNamed) (channel : CoherentNamed)
    (target : Coordinate) (positive : 0 < target) : Gaussian :=
  let named := CCL.ProgressiveFiniteTable.sharedName
    budget channel target positive
  (named.process.ball named.state).center

def SharedReadingsPossible (budget : List CoherentNamed) :
    (channels : List CoherentNamed) → (readings : List Gaussian) →
      (target : Coordinate) → 0 < target → Prop
  | [], [], _target, _positive => True
  | channel :: channels, reading :: readings, target, positive =>
      let named := CCL.ProgressiveFiniteTable.sharedName
        budget channel target positive
      named.process.Possible named.state reading ∧
        SharedReadingsPossible budget channels readings target positive
  | _, _, _target, _positive => False

def sharedCenters (budget channels : List CoherentNamed)
    (target : Coordinate) (positive : 0 < target) : List Gaussian :=
  channels.map (fun channel => sharedCenter budget channel target positive)

theorem sharedReadings_close : ∀ (budget channels : List CoherentNamed)
    (readings : List Gaussian) (target : Coordinate)
    (positive : 0 < target),
    SharedReadingsPossible budget channels readings target positive →
      EntriesClose readings (sharedCenters budget channels target positive)
        target
  | budget, [], [], target, positive, _possible => trivial
  | budget, [], _ :: _, target, positive, possible => by
      simp only [SharedReadingsPossible] at possible
  | budget, _ :: _, [], target, positive, possible => by
      simp only [SharedReadingsPossible] at possible
  | budget, channel :: channels, reading :: readings, target, positive,
      possible => by
      rcases possible with ⟨headPossible, tailPossible⟩
      constructor
      · let named := CCL.ProgressiveFiniteTable.sharedName
          budget channel target positive
        exact (named.process.possible_inside headPossible).trans
          (CCL.ProgressiveFiniteTable.sharedName_radius_lt
            budget channel positive).le
      · exact sharedReadings_close budget channels readings target positive
          tailPossible

/-- Paper-facing transport theorem for every finite progressive coefficient
table, including tables produced by arithmetic or finite composition. -/
theorem progressive_eval_error_le (channels : List CoherentNamed)
    (readings : List Gaussian) (input : Gaussian) (target : Coordinate)
    (positive : 0 < target)
    (possible : SharedReadingsPossible channels channels readings target
      positive) :
    normSq (eval readings input -
        eval (sharedCenters channels channels target positive) input) ≤
      evaluationErrorBudget readings.length target (normSq input) :=
  eval_error_le readings (sharedCenters channels channels target positive)
    input target (sharedReadings_close channels channels readings target
      positive possible)

/-! ## Explicit finite truncation -/

/-- Quadrance budget for evaluating one displayed finite coefficient list. -/
def coefficientNormBudget : List Gaussian → Coordinate → Coordinate
  | [], _ => 0
  | coefficient :: remaining, inputNormSq =>
      2 * (normSq coefficient +
        inputNormSq * coefficientNormBudget remaining inputNormSq)

theorem coefficientNormBudget_nonneg : ∀ coefficients inputNormSq,
    0 ≤ inputNormSq → 0 ≤ coefficientNormBudget coefficients inputNormSq
  | [], inputNormSq, _inputNonnegative => le_rfl
  | coefficient :: remaining, inputNormSq, inputNonnegative =>
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg (normSq_nonneg coefficient)
          (RFAP.ConstructiveFraction.mul_nonneg_direct inputNonnegative
            (coefficientNormBudget_nonneg remaining inputNormSq
              inputNonnegative)))

theorem eval_normSq_le : ∀ coefficients (input : Gaussian),
    normSq (eval coefficients input) ≤
      coefficientNormBudget coefficients (normSq input)
  | [], input => by
      change normSq (0 : Gaussian) ≤ 0
      rw [normSq_zero]
  | coefficient :: remaining, input => by
      change normSq (coefficient + input * eval remaining input) ≤ _
      calc
        normSq (coefficient + input * eval remaining input) ≤
            2 * (normSq coefficient +
              normSq (input * eval remaining input)) :=
          normSq_add_le_two _ _
        _ = 2 * (normSq coefficient +
              normSq input * normSq (eval remaining input)) := by
          rw [normSq_mul]
        _ ≤ 2 * (normSq coefficient +
              normSq input *
                coefficientNormBudget remaining (normSq input)) := by
          apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
            (by decide)
          exact add_le_add le_rfl
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (eval_normSq_le remaining input) (normSq_nonneg input))
        _ = coefficientNormBudget (coefficient :: remaining)
            (normSq input) := rfl

theorem eval_append : ∀ (retained discarded : List Gaussian)
    (input : Gaussian),
    eval (retained ++ discarded) input =
      eval retained input + input ^ retained.length * eval discarded input
  | [], discarded, input => by
      change eval discarded input = 0 + 1 * eval discarded input
      rw [RFAP.ConstructiveGaussian.Gaussian.one_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_add]
  | coefficient :: remaining, discarded, input => by
      rw [List.cons_append]
      simp only [eval, List.length_cons]
      rw [eval_append remaining discarded input, pow_succ]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im] <;> ring1

/-- Exact finite truncation error: only the explicitly discarded displayed
tail is charged.  There is no unmentioned infinite remainder. -/
theorem truncation_error_le (retained discarded : List Gaussian)
    (input : Gaussian) :
    normSq (eval (retained ++ discarded) input - eval retained input) ≤
      normSq (input ^ retained.length) *
        coefficientNormBudget discarded (normSq input) := by
  rw [eval_append]
  have identity :
      eval retained input + input ^ retained.length * eval discarded input -
          eval retained input =
        input ^ retained.length * eval discarded input := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im] <;> ring1
  rw [identity, normSq_mul]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    (eval_normSq_le discarded input)
    (normSq_nonneg (input ^ retained.length))

/-! ## Direct wrappers for the progressive higher-jet constructors -/

theorem TaylorJet.mul_evaluation_error
    (left right : CCL.ProgressiveHigherJet.TaylorJet)
    (readings : List Gaussian) (input : Gaussian) (target : Coordinate)
    (positive : 0 < target)
    (possible : SharedReadingsPossible
      (left.mul right).coefficients (left.mul right).coefficients readings
      target positive) :
    normSq (eval readings input -
        eval (sharedCenters (left.mul right).coefficients
          (left.mul right).coefficients target positive) input) ≤
      evaluationErrorBudget readings.length target (normSq input) :=
  progressive_eval_error_le (left.mul right).coefficients readings input target
    positive possible

theorem TaylorJet.compose_evaluation_error
    (outer inner : CCL.ProgressiveHigherJet.TaylorJet)
    (readings : List Gaussian) (input : Gaussian) (target : Coordinate)
    (positive : 0 < target)
    (possible : SharedReadingsPossible
      (outer.compose inner).coefficients (outer.compose inner).coefficients
      readings target positive) :
    normSq (eval readings input -
        eval (sharedCenters (outer.compose inner).coefficients
          (outer.compose inner).coefficients target positive) input) ≤
      evaluationErrorBudget readings.length target (normSq input) :=
  progressive_eval_error_le (outer.compose inner).coefficients readings input
    target positive possible

/-! ## Displayed finite-dimensional directional transport -/

def directionalEval : List Gaussian → List Gaussian → Gaussian
  | coefficient :: coefficients, direction :: directions =>
      coefficient * direction + directionalEval coefficients directions
  | _, _ => 0

def directionalErrorBudget : List Gaussian → Coordinate → Coordinate
  | [], _ => 0
  | direction :: directions, coefficientAllowance =>
      2 * (normSq direction * coefficientAllowance +
        directionalErrorBudget directions coefficientAllowance)

theorem directionalErrorBudget_nonneg : ∀ directions
    {coefficientAllowance : Coordinate}, 0 ≤ coefficientAllowance →
      0 ≤ directionalErrorBudget directions coefficientAllowance
  | [], _coefficientAllowance, _nonnegative => le_rfl
  | direction :: directions, coefficientAllowance, nonnegative =>
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            (normSq_nonneg direction) nonnegative)
          (directionalErrorBudget_nonneg directions nonnegative))

theorem directional_error_le : ∀ (actual displayed directions : List Gaussian)
    (coefficientAllowance : Coordinate),
    actual.length = directions.length →
    displayed.length = directions.length →
    EntriesClose actual displayed coefficientAllowance →
      normSq (directionalEval actual directions -
        directionalEval displayed directions) ≤
          directionalErrorBudget directions coefficientAllowance
  | [], [], [], coefficientAllowance, _actualLength, _displayedLength,
      _valid => by
      change normSq ((0 : Gaussian) - 0) ≤ 0
      rw [RFAP.ConstructiveGaussian.Gaussian.sub_self, normSq_zero]
  | [], [], _ :: _, coefficientAllowance, actualLength, displayedLength,
      valid => by
      simp only [List.length_nil, List.length_cons] at actualLength
      exact False.elim (Nat.noConfusion actualLength)
  | [], _ :: _, directions, coefficientAllowance, actualLength,
      displayedLength, valid => by
      simp only [EntriesClose] at valid
  | _ :: _, [], directions, coefficientAllowance, actualLength,
      displayedLength, valid => by
      simp only [EntriesClose] at valid
  | actual :: actualTail, displayed :: displayedTail, [],
      coefficientAllowance, actualLength, displayedLength, valid => by
      simp only [List.length_cons, List.length_nil] at actualLength
      exact False.elim (Nat.noConfusion actualLength)
  | actual :: actualTail, displayed :: displayedTail,
      direction :: directions, coefficientAllowance, actualLength,
      displayedLength, valid => by
      rcases valid with ⟨headClose, tailValid⟩
      have actualTailLength : actualTail.length = directions.length := by
        simp only [List.length_cons] at actualLength
        exact Nat.add_right_cancel actualLength
      have displayedTailLength : displayedTail.length = directions.length := by
        simp only [List.length_cons] at displayedLength
        exact Nat.add_right_cancel displayedLength
      have identity :
          directionalEval (actual :: actualTail) (direction :: directions) -
              directionalEval (displayed :: displayedTail)
                (direction :: directions) =
            (actual - displayed) * direction +
              (directionalEval actualTail directions -
                directionalEval displayedTail directions) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [directionalEval, sub_re, sub_im, add_re, add_im, mul_re,
            mul_im] <;> ring1
      rw [identity]
      calc
        normSq ((actual - displayed) * direction +
            (directionalEval actualTail directions -
              directionalEval displayedTail directions)) ≤
          2 * (normSq ((actual - displayed) * direction) +
            normSq (directionalEval actualTail directions -
              directionalEval displayedTail directions)) :=
          normSq_add_le_two _ _
        _ = 2 * (normSq direction * normSq (actual - displayed) +
            normSq (directionalEval actualTail directions -
              directionalEval displayedTail directions)) := by
          rw [normSq_mul]
          ring1
        _ ≤ 2 * (normSq direction * coefficientAllowance +
            directionalErrorBudget directions coefficientAllowance) := by
          apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
            (by decide)
          exact add_le_add
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              headClose (normSq_nonneg direction))
            (directional_error_le actualTail displayedTail directions
              coefficientAllowance actualTailLength displayedTailLength
              tailValid)
        _ = directionalErrorBudget (direction :: directions)
            coefficientAllowance := rfl

/-- Every displayed natural-number-arity directional table receives a finite
error budget; unequal arities are rejected by the two length premises. -/
theorem MultivariableFirstJet.directional_evaluation_error
    (jet : CCL.ProgressiveHigherJet.MultivariableFirstJet)
    (readings direction : List Gaussian) (target : Coordinate)
    (positive : 0 < target)
    (readingLength : readings.length = direction.length)
    (directionLength : direction.length = jet.partials.length)
    (possible : SharedReadingsPossible jet.partials jet.partials readings
      target positive) :
    normSq (directionalEval readings direction -
        directionalEval
          (sharedCenters jet.partials jet.partials target positive) direction) ≤
      directionalErrorBudget direction target := by
  apply directional_error_le readings
    (sharedCenters jet.partials jet.partials target positive) direction target
    readingLength
  · unfold sharedCenters
    rw [List.length_map]
    exact directionLength.symm
  · exact sharedReadings_close jet.partials jet.partials readings target
      positive possible

end CCL.ProgressiveTaylorError
