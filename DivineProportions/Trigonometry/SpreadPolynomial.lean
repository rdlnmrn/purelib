import mathlib.Tactic.QuotientFreeRing
import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.QuadrupleSpread

/-!
# Divine Proportions, Chapter 8: spread polynomials

Spread polynomials are primitive-recursive finite expressions.  No sequence
or limit object is introduced: evaluating index `n` performs exactly `n`
finite recurrence steps in the coefficient field.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Theorem 56 (Three equal spreads). -/
theorem three_equal_spreads [DecidableEq K]
    (line₀ line₁ line₂ line₃ : Line K)
    (line₀NonNull : ¬ line₀.IsNull) (line₁NonNull : ¬ line₁.IsNull)
    (line₂NonNull : ¬ line₂.IsNull) (line₃NonNull : ¬ line₃.IsNull)
    (firstEquality :
      spread line₀ line₁ line₀NonNull line₁NonNull =
        spread line₁ line₂ line₁NonNull line₂NonNull)
    (secondEquality :
      spread line₁ line₂ line₁NonNull line₂NonNull =
        spread line₂ line₃ line₂NonNull line₃NonNull)
    (notParallel : ¬ line₀.Parallel line₂) :
    let s := spread line₀ line₁ line₀NonNull line₁NonNull
    let r := spread line₀ line₃ line₀NonNull line₃NonNull
    r = s ∨ r = s * (3 - 4 * s) ^ 2 := by
  dsimp only
  let s := spread line₀ line₁ line₀NonNull line₁NonNull
  let q := spread line₀ line₂ line₀NonNull line₂NonNull
  let r := spread line₀ line₃ line₀NonNull line₃NonNull
  have middleAlternatives := equal_spreads line₀ line₁ line₂ line₀NonNull
    line₁NonNull line₂NonNull firstEquality
  change q = 0 ∨ q = 4 * s * (1 - s) at middleAlternatives
  have qNonzero : q ≠ 0 := by
    intro qZero
    apply notParallel
    exact (spread_eq_zero_iff_parallel line₀ line₂ line₀NonNull
      line₂NonNull).1 qZero
  have qEquation : q = 4 * s * (1 - s) := by
    rcases middleAlternatives with qZero | qValue
    · exact False.elim (qNonzero qZero)
    · exact qValue
  have thirdAdjacent :
      spread line₂ line₃ line₂NonNull line₃NonNull = s := by
    exact (firstEquality.trans secondEquality).symm
  have triple := three_lines_form_spreadTriple line₀ line₂ line₃
    line₀NonNull line₂NonNull line₃NonNull
  change SpreadTriple
    (spread line₂ line₃ line₂NonNull line₃NonNull) r q at triple
  rw [thirdAdjacent, qEquation] at triple
  have factorProduct :
      (r - s) * (r - s * (3 - 4 * s) ^ 2) = 0 := by
    calc
      (r - s) * (r - s * (3 - 4 * s) ^ 2) =
          -tripleSpreadFunction s r (4 * s * (1 - s)) := by
            unfold tripleSpreadFunction
            ring1
      _ = 0 := by
        unfold SpreadTriple at triple
        rw [triple]
        ring1
  by_cases firstFactorZero : r - s = 0
  · left
    exact sub_eq_zero.mp firstFactorZero
  · right
    have secondFactorZero : r - s * (3 - 4 * s) ^ 2 = 0 := by
      by_cases secondFactorCase : r - s * (3 - 4 * s) ^ 2 = 0
      · exact secondFactorCase
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero firstFactorZero secondFactorCase)
            factorProduct)
    exact sub_eq_zero.mp secondFactorZero

/-- Exercise 8.1.  Once the first three-step branch is selected, the next
Triple-spread equation has exactly the two displayed finite roots. -/
theorem exercise_8_1 [DecidableEq K]
    (line₀ line₃ line₄ : Line K)
    (line₀NonNull : ¬ line₀.IsNull) (line₃NonNull : ¬ line₃.IsNull)
    (line₄NonNull : ¬ line₄.IsNull)
    (value : K)
    (adjacentValue :
      spread line₃ line₄ line₃NonNull line₄NonNull = value)
    (threeStepValue :
      spread line₀ line₃ line₀NonNull line₃NonNull =
        value * (3 - 4 * value) ^ 2) :
    let result := spread line₀ line₄ line₀NonNull line₄NonNull
    result = 4 * value * (1 - value) ∨
      result = 16 * value * (1 - value) * (1 - 2 * value) ^ 2 := by
  dsimp only
  let result := spread line₀ line₄ line₀NonNull line₄NonNull
  have triple := three_lines_form_spreadTriple line₀ line₃ line₄
    line₀NonNull line₃NonNull line₄NonNull
  change SpreadTriple
    (spread line₃ line₄ line₃NonNull line₄NonNull)
    result
    (spread line₀ line₃ line₀NonNull line₃NonNull) at triple
  rw [adjacentValue, threeStepValue] at triple
  have factorProduct :
      (result - 4 * value * (1 - value)) *
        (result - 16 * value * (1 - value) * (1 - 2 * value) ^ 2) = 0 := by
    calc
      (result - 4 * value * (1 - value)) *
          (result - 16 * value * (1 - value) * (1 - 2 * value) ^ 2) =
        -tripleSpreadFunction value result
          (value * (3 - 4 * value) ^ 2) := by
            unfold tripleSpreadFunction
            ring1
      _ = 0 := by rw [triple]; ring1
  by_cases firstZero : result - 4 * value * (1 - value) = 0
  · left
    exact sub_eq_zero.mp firstZero
  · right
    have secondZero :
        result - 16 * value * (1 - value) * (1 - 2 * value) ^ 2 = 0 := by
      by_cases candidateZero :
          result - 16 * value * (1 - value) * (1 - 2 * value) ^ 2 = 0
      · exact candidateZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero firstZero candidateZero)
            factorProduct)
    exact sub_eq_zero.mp secondZero

/-- Primitive-recursive definition of the spread polynomial `Sₙ`. -/
def spreadPolynomial {R : Type*} [CommRing R] : Nat → R → R
  | 0, _ => 0
  | 1, value => value
  | index + 2, value =>
      2 * (1 - 2 * value) * spreadPolynomial (index + 1) value -
        spreadPolynomial index value + 2 * value

@[simp] theorem spreadPolynomial_zero
    {R : Type*} [CommRing R] (value : R) :
    spreadPolynomial 0 value = 0 := rfl

@[simp] theorem spreadPolynomial_one
    {R : Type*} [CommRing R] (value : R) :
    spreadPolynomial 1 value = value := rfl

@[simp] theorem spreadPolynomial_succ_succ
    {R : Type*} [CommRing R] (index : Nat) (value : R) :
    spreadPolynomial (index + 2) value =
      2 * (1 - 2 * value) * spreadPolynomial (index + 1) value -
        spreadPolynomial index value + 2 * value := rfl

private theorem spreadTriple_next
    (previous current value : K)
    (triple : SpreadTriple previous value current) :
    SpreadTriple current value
      (2 * (1 - 2 * value) * current - previous + 2 * value) := by
  unfold SpreadTriple tripleSpreadFunction at triple ⊢
  calc
    (current + value +
            (2 * (1 - 2 * value) * current - previous + 2 * value)) ^ 2 -
          2 * (current ^ 2 + value ^ 2 +
            (2 * (1 - 2 * value) * current - previous + 2 * value) ^ 2) -
          4 * current * value *
            (2 * (1 - 2 * value) * current - previous + 2 * value) =
      (previous + value + current) ^ 2 -
        2 * (previous ^ 2 + value ^ 2 + current ^ 2) -
        4 * previous * value * current := by ring1
    _ = 0 := triple

/-- Theorem 57 (Recursive spreads), shifted to the cleaner finite index
`{Sₙ(s), s, Sₙ₊₁(s)}` for every natural `n`. -/
theorem recursive_spreads (index : Nat) (value : K) :
    SpreadTriple (spreadPolynomial index value) value
      (spreadPolynomial (index + 1) value) := by
  induction index with
  | zero =>
      unfold spreadPolynomial SpreadTriple tripleSpreadFunction
      ring1
  | succ index inductionHypothesis =>
      have next := spreadTriple_next
        (spreadPolynomial index value)
        (spreadPolynomial (index + 1) value) value inductionHypothesis
      simpa only [Nat.succ_eq_add_one, spreadPolynomial_succ_succ] using next

/-- A second-order spread-polynomial orbit repeats at every later requested
index once two consecutive finite seeds repeat. -/
theorem spreadPolynomial_period
    (period : Nat) (value : K)
    (zeroSeed : spreadPolynomial period value = 0)
    (oneSeed : spreadPolynomial (period + 1) value = value)
    (index : Nat) :
    spreadPolynomial (index + period) value =
      spreadPolynomial index value := by
  let repeatsAt := fun current : Nat =>
    spreadPolynomial (current + period) value =
      spreadPolynomial current value
  have allPairs : ∀ current : Nat,
      repeatsAt current ∧ repeatsAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · unfold repeatsAt
          simpa only [Nat.zero_add, spreadPolynomial_zero] using zeroSeed
        · unfold repeatsAt
          rw [show 0 + 1 + period = period + 1 by omega0]
          rw [oneSeed]
          change value = spreadPolynomial 1 value
          rw [spreadPolynomial_one]
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · unfold repeatsAt
          have middleRepeat :
              spreadPolynomial (current + period + 1) value =
                spreadPolynomial (current + 1) value := by
            calc
              spreadPolynomial (current + period + 1) value =
                  spreadPolynomial (current + 1 + period) value := by
                congr 1
                omega0
              _ = spreadPolynomial (current + 1) value :=
                inductionHypothesis.2
          rw [show Nat.succ current + 1 + period =
            (current + period) + 2 by omega0]
          rw [show Nat.succ current + 1 = current + 2 by omega0]
          rw [spreadPolynomial_succ_succ, spreadPolynomial_succ_succ,
            inductionHypothesis.1, middleRepeat]
  exact (allPairs index).1

/-- The even and odd addition seeds for the spread-polynomial recurrence.
Both identities are proved together by finite induction; the only geometric
input is the already algebraic `SpreadTriple` recurrence invariant. -/
private theorem spreadPolynomial_double_and_odd (index : Nat) (value : K) :
    spreadPolynomial (index + index) value =
        4 * spreadPolynomial index value *
          (1 - spreadPolynomial index value) ∧
      spreadPolynomial (index + index + 1) value + value =
        2 * (spreadPolynomial (index + 1) value +
          spreadPolynomial index value -
          2 * spreadPolynomial (index + 1) value *
            spreadPolynomial index value) := by
  induction index with
  | zero =>
      constructor <;> unfold spreadPolynomial <;> ring1
  | succ index inductionHypothesis =>
      rcases inductionHypothesis with ⟨evenFormula, oddFormula⟩
      have triple := recursive_spreads index value
      unfold SpreadTriple at triple
      have oddResolved :
          spreadPolynomial (index + index + 1) value =
            2 * (spreadPolynomial (index + 1) value +
              spreadPolynomial index value -
              2 * spreadPolynomial (index + 1) value *
                spreadPolynomial index value) - value := by
        calc
          spreadPolynomial (index + index + 1) value =
              (spreadPolynomial (index + index + 1) value + value) -
                value := by ring1
          _ = 2 * (spreadPolynomial (index + 1) value +
                spreadPolynomial index value -
                2 * spreadPolynomial (index + 1) value *
                  spreadPolynomial index value) - value := by
              rw [oddFormula]
      have nextEven :
          spreadPolynomial (Nat.succ index + Nat.succ index) value =
            4 * spreadPolynomial (Nat.succ index) value *
              (1 - spreadPolynomial (Nat.succ index) value) := by
        rw [show Nat.succ index + Nat.succ index =
          index + index + 2 by
            simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm]]
        rw [spreadPolynomial_succ_succ, oddResolved, evenFormula]
        calc
          2 * (1 - 2 * value) *
                (2 * (spreadPolynomial (index + 1) value +
                    spreadPolynomial index value -
                    2 * spreadPolynomial (index + 1) value *
                      spreadPolynomial index value) - value) -
              4 * spreadPolynomial index value *
                (1 - spreadPolynomial index value) + 2 * value =
            4 * spreadPolynomial (index + 1) value *
                (1 - spreadPolynomial (index + 1) value) -
              4 * tripleSpreadFunction
                (spreadPolynomial index value) value
                (spreadPolynomial (index + 1) value) := by
                  unfold tripleSpreadFunction
                  ring1
          _ = 4 * spreadPolynomial (Nat.succ index) value *
                (1 - spreadPolynomial (Nat.succ index) value) := by
              rw [triple]
              simp only [mul_zero, sub_zero, Nat.succ_eq_add_one]
      have nextEvenNormalized :
          spreadPolynomial (index + index + 2) value =
            4 * spreadPolynomial (index + 1) value *
              (1 - spreadPolynomial (index + 1) value) := by
        rw [show index + index + 2 =
          Nat.succ index + Nat.succ index by
            simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm]]
        simpa only [Nat.succ_eq_add_one] using nextEven
      have nextOdd :
          spreadPolynomial
              (Nat.succ index + Nat.succ index + 1) value + value =
            2 * (spreadPolynomial (Nat.succ index + 1) value +
              spreadPolynomial (Nat.succ index) value -
              2 * spreadPolynomial (Nat.succ index + 1) value *
                spreadPolynomial (Nat.succ index) value) := by
        rw [show Nat.succ index + Nat.succ index + 1 =
          (index + index + 1) + 2 by
            simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm]]
        rw [spreadPolynomial_succ_succ, nextEvenNormalized, oddResolved]
        rw [show Nat.succ index + 1 = index + 2 by rfl]
        rw [spreadPolynomial_succ_succ]
        ring1
      exact ⟨nextEven, nextOdd⟩

/-- The addition-law statement at one displayed offset.  Keeping the offset
as an explicit argument avoids reasoning about equality of proposition-valued
functions in the simultaneous induction below. -/
private def spreadPolynomialAdditionAt
    (step : Nat) (value : K) (current : Nat) : Prop :=
  spreadPolynomial (current + step + step) value +
      spreadPolynomial current value =
    2 * (spreadPolynomial (current + step) value +
      spreadPolynomial step value -
      2 * spreadPolynomial (current + step) value *
        spreadPolynomial step value)

/-- Finite addition law for spread polynomials.  In the usual symmetric
notation this is
`S_(a+2b) + S_a = 2(S_(a+b) + S_b - 2 S_(a+b) S_b)`.
It is the recurrence identity needed for composition and is valid in every
constructive explicit field, without a characteristic restriction. -/
theorem spread_polynomial_addition
    (offset step : Nat) (value : K) :
    spreadPolynomial (offset + step + step) value +
        spreadPolynomial offset value =
      2 * (spreadPolynomial (offset + step) value +
        spreadPolynomial step value -
        2 * spreadPolynomial (offset + step) value *
          spreadPolynomial step value) := by
  have allPairs : ∀ current : Nat,
      spreadPolynomialAdditionAt step value current ∧
        spreadPolynomialAdditionAt step value (current + 1) := by
    intro current
    induction current with
    | zero =>
        rcases spreadPolynomial_double_and_odd step value with
          ⟨evenFormula, oddFormula⟩
        constructor
        · unfold spreadPolynomialAdditionAt
          simp only [Nat.zero_add, spreadPolynomial_zero, add_zero]
          rw [evenFormula]
          ring1
        · unfold spreadPolynomialAdditionAt
          rw [show 0 + 1 + step + step = step + step + 1 by
            simp only [Nat.zero_add, Nat.add_assoc, Nat.add_comm]]
          rw [show 0 + 1 + step = step + 1 by
            simp only [Nat.zero_add, Nat.add_comm]]
          rw [spreadPolynomial_one]
          exact oddFormula
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · change spreadPolynomialAdditionAt step value
            (Nat.succ current + 1)
          have currentFormula :
              spreadPolynomial (current + step + step) value +
                  spreadPolynomial current value =
                2 * (spreadPolynomial (current + step) value +
                  spreadPolynomial step value -
                  2 * spreadPolynomial (current + step) value *
                    spreadPolynomial step value) := by
            exact inductionHypothesis.1
          have nextFormula :
              spreadPolynomial (current + step + step + 1) value +
                  spreadPolynomial (current + 1) value =
                2 * (spreadPolynomial (current + step + 1) value +
                  spreadPolynomial step value -
                  2 * spreadPolynomial (current + step + 1) value *
                    spreadPolynomial step value) := by
            simpa only [spreadPolynomialAdditionAt, Nat.add_assoc,
              Nat.add_left_comm,
              Nat.add_comm] using inductionHypothesis.2
          unfold spreadPolynomialAdditionAt
          rw [show Nat.succ current + 1 + step + step =
            (current + step + step) + 2 by
              simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]]
          rw [show Nat.succ current + 1 = current + 2 by rfl]
          rw [show Nat.succ current + 1 + step =
            (current + step) + 2 by
              simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]]
          rw [spreadPolynomial_succ_succ,
            spreadPolynomial_succ_succ,
            spreadPolynomial_succ_succ]
          calc
            (2 * (1 - 2 * value) *
                    spreadPolynomial (current + step + step + 1) value -
                  spreadPolynomial (current + step + step) value +
                  2 * value) +
                (2 * (1 - 2 * value) *
                    spreadPolynomial (current + 1) value -
                  spreadPolynomial current value + 2 * value) =
              2 * (1 - 2 * value) *
                  (spreadPolynomial (current + step + step + 1) value +
                    spreadPolynomial (current + 1) value) -
                (spreadPolynomial (current + step + step) value +
                  spreadPolynomial current value) + 4 * value := by ring1
            _ = 2 * (1 - 2 * value) *
                  (2 * (spreadPolynomial (current + step + 1) value +
                    spreadPolynomial step value -
                    2 * spreadPolynomial (current + step + 1) value *
                      spreadPolynomial step value)) -
                2 * (spreadPolynomial (current + step) value +
                  spreadPolynomial step value -
                  2 * spreadPolynomial (current + step) value *
                    spreadPolynomial step value) + 4 * value := by
                      rw [nextFormula, currentFormula]
            _ = 2 *
                ((2 * (1 - 2 * value) *
                    spreadPolynomial (current + step + 1) value -
                    spreadPolynomial (current + step) value + 2 * value) +
                  spreadPolynomial step value -
                  2 *
                    (2 * (1 - 2 * value) *
                        spreadPolynomial (current + step + 1) value -
                      spreadPolynomial (current + step) value + 2 * value) *
                    spreadPolynomial step value) := by ring1
  exact (allPairs offset).1

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

/-- The denominator-free spread formula needs only one formal offset whose
square is `-4s(1-s)`.  This commutative-ring form is stronger than the
source's presentation through two separately selected square roots. -/
theorem spread_polynomial_offset_formula_cleared
    {R : Type*} [CommRing R]
    (value offset : R)
    (offsetEquation : offset ^ 2 = -(4 * value * (1 - value)))
    (index : Nat) :
    4 * spreadPolynomial index value =
      2 - (1 - 2 * value + offset) ^ index -
        (1 - 2 * value - offset) ^ index := by
  let center := 1 - 2 * value
  let positive := center + offset
  let negative := center - offset
  have positiveQuadratic :
      positive ^ 2 = 2 * center * positive - 1 := by
    unfold positive center
    calc
      (1 - 2 * value + offset) ^ 2 =
          (1 - 2 * value) ^ 2 +
            2 * (1 - 2 * value) * offset + offset ^ 2 := by ring1
      _ = (1 - 2 * value) ^ 2 +
            2 * (1 - 2 * value) * offset -
              4 * value * (1 - value) := by
                rw [offsetEquation]
                ring1
      _ = 2 * (1 - 2 * value) *
            (1 - 2 * value + offset) - 1 := by ring1
  have negativeQuadratic :
      negative ^ 2 = 2 * center * negative - 1 := by
    unfold negative center
    calc
      (1 - 2 * value - offset) ^ 2 =
          (1 - 2 * value) ^ 2 -
            2 * (1 - 2 * value) * offset + offset ^ 2 := by ring1
      _ = (1 - 2 * value) ^ 2 -
            2 * (1 - 2 * value) * offset -
              4 * value * (1 - value) := by
                rw [offsetEquation]
                ring1
      _ = 2 * (1 - 2 * value) *
            (1 - 2 * value - offset) - 1 := by ring1
  change
    4 * spreadPolynomial index value =
      2 - positive ^ index - negative ^ index
  induction index using Nat.strong_induction_on with
  | h index inductionHypothesis =>
      cases index with
      | zero =>
          unfold spreadPolynomial
          ring1
      | succ index =>
          cases index with
          | zero =>
              unfold spreadPolynomial positive negative center
              ring1
          | succ index =>
              let priorIndex := index
              have previousFormula := inductionHypothesis (priorIndex + 1)
                (Nat.lt_succ_self (priorIndex + 1))
              have beforePreviousFormula := inductionHypothesis priorIndex
                (Nat.lt_trans (Nat.lt_succ_self priorIndex)
                  (Nat.lt_succ_self (priorIndex + 1)))
              have positiveRecurrence :
                  positive ^ (priorIndex + 2) =
                    2 * center * positive ^ (priorIndex + 1) -
                      positive ^ priorIndex := by
                calc
                  positive ^ (priorIndex + 2) =
                      positive ^ priorIndex * positive ^ 2 := by
                        rw [pow_add]
                  _ = positive ^ priorIndex *
                      (2 * center * positive - 1) := by
                        rw [positiveQuadratic]
                  _ = 2 * center * (positive ^ priorIndex * positive) -
                      positive ^ priorIndex := by ring1
                  _ = 2 * center * positive ^ (priorIndex + 1) -
                      positive ^ priorIndex := by rw [pow_succ]
              have negativeRecurrence :
                  negative ^ (priorIndex + 2) =
                    2 * center * negative ^ (priorIndex + 1) -
                      negative ^ priorIndex := by
                calc
                  negative ^ (priorIndex + 2) =
                      negative ^ priorIndex * negative ^ 2 := by
                        rw [pow_add]
                  _ = negative ^ priorIndex *
                      (2 * center * negative - 1) := by
                        rw [negativeQuadratic]
                  _ = 2 * center * (negative ^ priorIndex * negative) -
                      negative ^ priorIndex := by ring1
                  _ = 2 * center * negative ^ (priorIndex + 1) -
                      negative ^ priorIndex := by rw [pow_succ]
              change
                4 * spreadPolynomial (priorIndex + 2) value =
                  2 - positive ^ (priorIndex + 2) -
                    negative ^ (priorIndex + 2)
              rw [spreadPolynomial_succ_succ]
              calc
                4 *
                    (2 * (1 - 2 * value) *
                        spreadPolynomial (priorIndex + 1) value -
                      spreadPolynomial priorIndex value + 2 * value) =
                  2 * center *
                      (4 * spreadPolynomial (priorIndex + 1) value) -
                    4 * spreadPolynomial priorIndex value + 8 * value := by
                      unfold center
                      ring1
                _ = 2 * center *
                      (2 - positive ^ (priorIndex + 1) -
                        negative ^ (priorIndex + 1)) -
                    (2 - positive ^ priorIndex - negative ^ priorIndex) +
                    8 * value := by
                      rw [previousFormula, beforePreviousFormula]
                _ = 2 - positive ^ (priorIndex + 2) -
                    negative ^ (priorIndex + 2) := by
                      rw [positiveRecurrence, negativeRecurrence]
                      unfold center
                      ring1

/-- Denominator-cleared form of Theorem 59. -/
theorem spread_polynomial_formula_cleared
    (value root imaginary : K)
    (rootEquation : 4 * value * (1 - value) = root ^ 2)
    (imaginaryEquation : imaginary ^ 2 = -1)
    (index : Nat) :
    4 * spreadPolynomial index value =
      2 - (1 - 2 * value + imaginary * root) ^ index -
        (1 - 2 * value - imaginary * root) ^ index := by
  let center := 1 - 2 * value
  let positive := center + imaginary * root
  let negative := center - imaginary * root
  have positiveQuadratic :
      positive ^ 2 = 2 * center * positive - 1 := by
    unfold positive center
    calc
      (1 - 2 * value + imaginary * root) ^ 2 =
          (1 - 2 * value) ^ 2 +
            2 * (1 - 2 * value) * imaginary * root +
            imaginary ^ 2 * root ^ 2 := by ring1
      _ = (1 - 2 * value) ^ 2 +
            2 * (1 - 2 * value) * imaginary * root -
            4 * value * (1 - value) := by
              rw [imaginaryEquation, ← rootEquation]
              ring1
      _ = 2 * (1 - 2 * value) *
            (1 - 2 * value + imaginary * root) - 1 := by ring1
  have negativeQuadratic :
      negative ^ 2 = 2 * center * negative - 1 := by
    unfold negative center
    calc
      (1 - 2 * value - imaginary * root) ^ 2 =
          (1 - 2 * value) ^ 2 -
            2 * (1 - 2 * value) * imaginary * root +
            imaginary ^ 2 * root ^ 2 := by ring1
      _ = (1 - 2 * value) ^ 2 -
            2 * (1 - 2 * value) * imaginary * root -
            4 * value * (1 - value) := by
              rw [imaginaryEquation, ← rootEquation]
              ring1
      _ = 2 * (1 - 2 * value) *
            (1 - 2 * value - imaginary * root) - 1 := by ring1
  change
    4 * spreadPolynomial index value =
      2 - positive ^ index - negative ^ index
  induction index using Nat.strong_induction_on with
  | h index inductionHypothesis =>
      cases index with
      | zero =>
          unfold spreadPolynomial
          ring1
      | succ index =>
          cases index with
          | zero =>
              unfold spreadPolynomial positive negative center
              ring1
          | succ index =>
              let priorIndex := index
              have previousFormula := inductionHypothesis (priorIndex + 1)
                (Nat.lt_succ_self (priorIndex + 1))
              have beforePreviousFormula := inductionHypothesis priorIndex
                (Nat.lt_trans (Nat.lt_succ_self priorIndex)
                  (Nat.lt_succ_self (priorIndex + 1)))
              have positiveRecurrence :
                  positive ^ (priorIndex + 2) =
                    2 * center * positive ^ (priorIndex + 1) -
                      positive ^ priorIndex := by
                calc
                  positive ^ (priorIndex + 2) =
                      positive ^ priorIndex * positive ^ 2 := by
                        rw [pow_add]
                  _ = positive ^ priorIndex *
                      (2 * center * positive - 1) := by
                        rw [positiveQuadratic]
                  _ = 2 * center * (positive ^ priorIndex * positive) -
                      positive ^ priorIndex := by ring1
                  _ = 2 * center * positive ^ (priorIndex + 1) -
                      positive ^ priorIndex := by rw [pow_succ]
              have negativeRecurrence :
                  negative ^ (priorIndex + 2) =
                    2 * center * negative ^ (priorIndex + 1) -
                      negative ^ priorIndex := by
                calc
                  negative ^ (priorIndex + 2) =
                      negative ^ priorIndex * negative ^ 2 := by
                        rw [pow_add]
                  _ = negative ^ priorIndex *
                      (2 * center * negative - 1) := by
                        rw [negativeQuadratic]
                  _ = 2 * center * (negative ^ priorIndex * negative) -
                      negative ^ priorIndex := by ring1
                  _ = 2 * center * negative ^ (priorIndex + 1) -
                      negative ^ priorIndex := by rw [pow_succ]
              change
                4 * spreadPolynomial (priorIndex + 2) value =
                  2 - positive ^ (priorIndex + 2) - negative ^ (priorIndex + 2)
              rw [spreadPolynomial_succ_succ]
              calc
                4 *
                    (2 * (1 - 2 * value) *
                        spreadPolynomial (priorIndex + 1) value -
                      spreadPolynomial priorIndex value + 2 * value) =
                  2 * center *
                      (4 * spreadPolynomial (priorIndex + 1) value) -
                    4 * spreadPolynomial priorIndex value + 8 * value := by
                      unfold center
                      ring1
                _ = 2 * center *
                      (2 - positive ^ (priorIndex + 1) -
                        negative ^ (priorIndex + 1)) -
                    (2 - positive ^ priorIndex - negative ^ priorIndex) +
                    8 * value := by
                      rw [previousFormula, beforePreviousFormula]
                _ = 2 - positive ^ (priorIndex + 2) -
                    negative ^ (priorIndex + 2) := by
                      rw [positiveRecurrence, negativeRecurrence]
                      unfold center
                      ring1

/-- Theorem 59 (Spread polynomial formula). -/
theorem spread_polynomial_formula
    (value root imaginary : K)
    (fourNonzero : (4 : K) ≠ 0)
    (rootEquation : 4 * value * (1 - value) = root ^ 2)
    (imaginaryEquation : imaginary ^ 2 = -1)
    (index : Nat) :
    spreadPolynomial index value =
      (2 - (1 - 2 * value + imaginary * root) ^ index -
        (1 - 2 * value - imaginary * root) ^ index) / 4 := by
  have cleared := spread_polynomial_formula_cleared value root imaginary
    rootEquation imaginaryEquation index
  apply eq_of_mul_eq_mul_right fourNonzero
  calc
    spreadPolynomial index value * 4 =
        4 * spreadPolynomial index value := by ring1
    _ = 2 - (1 - 2 * value + imaginary * root) ^ index -
        (1 - 2 * value - imaginary * root) ^ index := cleared
    _ = ((2 - (1 - 2 * value + imaginary * root) ^ index -
          (1 - 2 * value - imaginary * root) ^ index) / 4) * 4 :=
      (RFAP.ExplicitField.div_mul_cancel _ fourNonzero).symm

/-- Theorem 60 (Spread composition).  This is proved solely from the finite
recurrence and `spread_polynomial_addition`; unlike the book's informal
argument, it does not pass through an infinite reflection sequence or a
density/root-counting argument. -/
theorem spread_polynomial_composition
    (outer inner : Nat) (value : K) :
    spreadPolynomial outer (spreadPolynomial inner value) =
      spreadPolynomial (outer * inner) value := by
  let compositionAt := fun current : Nat =>
    spreadPolynomial current (spreadPolynomial inner value) =
      spreadPolynomial (current * inner) value
  have allPairs : ∀ current : Nat,
      compositionAt current ∧ compositionAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · unfold compositionAt
          simp only [spreadPolynomial_zero, Nat.zero_mul]
        · unfold compositionAt
          simp only [Nat.zero_add, spreadPolynomial_one, Nat.one_mul]
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · change compositionAt (Nat.succ current + 1)
          have currentFormula :
              spreadPolynomial current (spreadPolynomial inner value) =
                spreadPolynomial (current * inner) value := by
            exact inductionHypothesis.1
          have nextFormula :
              spreadPolynomial (current + 1)
                  (spreadPolynomial inner value) =
                spreadPolynomial ((current + 1) * inner) value := by
            exact inductionHypothesis.2
          unfold compositionAt
          rw [show Nat.succ current + 1 = current + 2 by rfl]
          rw [spreadPolynomial_succ_succ, currentFormula, nextFormula]
          have additionFormula := spread_polynomial_addition
            (current * inner) inner value
          calc
            2 * (1 - 2 * spreadPolynomial inner value) *
                  spreadPolynomial ((current + 1) * inner) value -
                spreadPolynomial (current * inner) value +
                2 * spreadPolynomial inner value =
              2 * (spreadPolynomial (current * inner + inner) value +
                    spreadPolynomial inner value -
                    2 * spreadPolynomial (current * inner + inner) value *
                      spreadPolynomial inner value) -
                spreadPolynomial (current * inner) value := by
                  rw [Nat.add_mul]
                  simp only [Nat.one_mul]
                  ring1
            _ = (spreadPolynomial
                    (current * inner + inner + inner) value +
                  spreadPolynomial (current * inner) value) -
                spreadPolynomial (current * inner) value := by
                  rw [additionFormula]
            _ = spreadPolynomial
                  (current * inner + inner + inner) value := by ring1
            _ = spreadPolynomial ((current + 2) * inner) value := by
                  apply congrArg (fun index => spreadPolynomial index value)
                  rw [Nat.add_mul, Nat.two_mul, ← Nat.add_assoc]
  exact (allPairs outer).1

/-- The commutativity consequence stated immediately after Theorem 60. -/
theorem spread_polynomial_composition_commutative
    (first second : Nat) (value : K) :
    spreadPolynomial first (spreadPolynomial second value) =
      spreadPolynomial second (spreadPolynomial first value) := by
  calc
    spreadPolynomial first (spreadPolynomial second value) =
        spreadPolynomial (first * second) value :=
      spread_polynomial_composition first second value
    _ = spreadPolynomial (second * first) value := by
      rw [Nat.mul_comm]
    _ = spreadPolynomial second (spreadPolynomial first value) :=
      (spread_polynomial_composition second first value).symm

/-- The associativity consequence stated immediately after Theorem 60,
expressed pointwise for the executable family. -/
theorem spread_polynomial_composition_associative
    (first second third : Nat) (value : K) :
    spreadPolynomial (first * second)
        (spreadPolynomial third value) =
      spreadPolynomial first
        (spreadPolynomial (second * third) value) := by
  calc
    spreadPolynomial (first * second) (spreadPolynomial third value) =
        spreadPolynomial ((first * second) * third) value :=
      spread_polynomial_composition (first * second) third value
    _ = spreadPolynomial (first * (second * third)) value := by
      rw [Nat.mul_assoc]
    _ = spreadPolynomial first
          (spreadPolynomial (second * third) value) :=
      (spread_polynomial_composition first (second * third) value).symm

end DivineProportions
