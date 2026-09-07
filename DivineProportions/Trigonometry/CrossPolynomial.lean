import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadPolynomial

/-!
# Divine Proportions, Chapter 8: cross polynomials

The cross-polynomial exercises are proved from their primitive recursion and
the already finite spread-polynomial recurrence.  Every index requests only a
bounded number of arithmetic steps.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The recursively defined cross polynomial `Cₙ`. -/
def crossPolynomial : Nat → K → K
  | 0, _ => 1
  | 1, value => value
  | index + 2, value =>
      2 * (2 * value - 1) * crossPolynomial (index + 1) value -
        crossPolynomial index value + 2 * (1 - value)

@[simp] theorem crossPolynomial_zero (value : K) :
    crossPolynomial 0 value = 1 := rfl

@[simp] theorem crossPolynomial_one (value : K) :
    crossPolynomial 1 value = value := rfl

@[simp] theorem crossPolynomial_succ_succ (index : Nat) (value : K) :
    crossPolynomial (index + 2) value =
      2 * (2 * value - 1) * crossPolynomial (index + 1) value -
        crossPolynomial index value + 2 * (1 - value) := rfl

/-- Exercise 8.17 in its strongest pointwise form: `Cₙ(c)=1-Sₙ(1-c)`. -/
theorem crossPolynomial_eq_one_sub_spreadPolynomial
    (index : Nat) (value : K) :
    crossPolynomial index value =
      1 - spreadPolynomial index (1 - value) := by
  let relationAt := fun current : Nat =>
    crossPolynomial current value =
      1 - spreadPolynomial current (1 - value)
  have allPairs : ∀ current : Nat,
      relationAt current ∧ relationAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · unfold relationAt crossPolynomial spreadPolynomial
          ring1
        · unfold relationAt crossPolynomial spreadPolynomial
          ring1
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · unfold relationAt
          rw [show Nat.succ current + 1 = current + 2 by omega0]
          rw [crossPolynomial_succ_succ, spreadPolynomial_succ_succ,
            inductionHypothesis.1, inductionHypothesis.2]
          ring1
  exact (allPairs index).1

/-- Exercise 8.14, with the source's `n≥1` shifted to the executable pair
`{Cₙ(c),c,Cₙ₊₁(c)}`. -/
theorem exercise_8_14 (index : Nat) (value : K) :
    (crossPolynomial index value + value +
          crossPolynomial (index + 1) value - 1) ^ 2 =
      4 * crossPolynomial index value * value *
        crossPolynomial (index + 1) value := by
  have triple := recursive_spreads index (1 - value)
  unfold SpreadTriple at triple
  rw [crossPolynomial_eq_one_sub_spreadPolynomial index value,
    crossPolynomial_eq_one_sub_spreadPolynomial (index + 1) value]
  apply sub_eq_zero.mp
  calc
    ((1 - spreadPolynomial index (1 - value)) + value +
          (1 - spreadPolynomial (index + 1) (1 - value)) - 1) ^ 2 -
        4 * (1 - spreadPolynomial index (1 - value)) * value *
          (1 - spreadPolynomial (index + 1) (1 - value)) =
      -tripleSpreadFunction
        (spreadPolynomial index (1 - value)) (1 - value)
        (spreadPolynomial (index + 1) (1 - value)) := by
          unfold tripleSpreadFunction
          ring1
    _ = 0 := by rw [triple]; ring1

/-- Exercise 8.15: the first seven cross polynomials, in both expanded and
factored forms printed by the source. -/
theorem exercise_8_15 (value : K) :
    crossPolynomial 0 value = 1 ∧
      crossPolynomial 1 value = value ∧
      crossPolynomial 2 value = 1 - 4 * value + 4 * value ^ 2 ∧
      crossPolynomial 2 value = (1 - 2 * value) ^ 2 ∧
      crossPolynomial 3 value =
        9 * value - 24 * value ^ 2 + 16 * value ^ 3 ∧
      crossPolynomial 3 value = value * (3 - 4 * value) ^ 2 ∧
      crossPolynomial 4 value =
        1 - 16 * value + 80 * value ^ 2 - 128 * value ^ 3 +
          64 * value ^ 4 ∧
      crossPolynomial 4 value = (1 - 8 * value + 8 * value ^ 2) ^ 2 ∧
      crossPolynomial 5 value =
        value * (5 - 20 * value + 16 * value ^ 2) ^ 2 ∧
      crossPolynomial 6 value =
        (1 - 2 * value) ^ 2 * (1 - 16 * value + 16 * value ^ 2) ^ 2 := by
  have valueTwo : crossPolynomial 2 value =
      1 - 4 * value + 4 * value ^ 2 := by
    change
      2 * (2 * value - 1) * crossPolynomial 1 value -
          crossPolynomial 0 value + 2 * (1 - value) =
        1 - 4 * value + 4 * value ^ 2
    rw [crossPolynomial_zero, crossPolynomial_one]
    ring1
  have valueThree : crossPolynomial 3 value =
      9 * value - 24 * value ^ 2 + 16 * value ^ 3 := by
    change
      2 * (2 * value - 1) * crossPolynomial 2 value -
          crossPolynomial 1 value + 2 * (1 - value) =
        9 * value - 24 * value ^ 2 + 16 * value ^ 3
    rw [valueTwo, crossPolynomial_one]
    ring1
  have valueFour : crossPolynomial 4 value =
      1 - 16 * value + 80 * value ^ 2 - 128 * value ^ 3 +
        64 * value ^ 4 := by
    change
      2 * (2 * value - 1) * crossPolynomial 3 value -
          crossPolynomial 2 value + 2 * (1 - value) =
        1 - 16 * value + 80 * value ^ 2 - 128 * value ^ 3 +
          64 * value ^ 4
    rw [valueThree, valueTwo]
    ring1
  have valueFive : crossPolynomial 5 value =
      value * (5 - 20 * value + 16 * value ^ 2) ^ 2 := by
    change
      2 * (2 * value - 1) * crossPolynomial 4 value -
          crossPolynomial 3 value + 2 * (1 - value) =
        value * (5 - 20 * value + 16 * value ^ 2) ^ 2
    rw [valueFour, valueThree]
    ring1
  have valueSix : crossPolynomial 6 value =
      (1 - 2 * value) ^ 2 *
        (1 - 16 * value + 16 * value ^ 2) ^ 2 := by
    change
      2 * (2 * value - 1) * crossPolynomial 5 value -
          crossPolynomial 4 value + 2 * (1 - value) =
        (1 - 2 * value) ^ 2 *
          (1 - 16 * value + 16 * value ^ 2) ^ 2
    rw [valueFive, valueFour]
    ring1
  exact ⟨crossPolynomial_zero value, crossPolynomial_one value,
    valueTwo, valueTwo.trans (by ring1), valueThree,
    valueThree.trans (by ring1), valueFour, valueFour.trans (by ring1),
    valueFive, valueSix⟩

/-- Exercise 8.16: cross-polynomial composition. -/
theorem cross_polynomial_composition
    (outer inner : Nat) (value : K) :
    crossPolynomial outer (crossPolynomial inner value) =
      crossPolynomial (outer * inner) value := by
  calc
    crossPolynomial outer (crossPolynomial inner value) =
        1 - spreadPolynomial outer
          (1 - crossPolynomial inner value) :=
      crossPolynomial_eq_one_sub_spreadPolynomial outer _
    _ = 1 - spreadPolynomial outer
          (spreadPolynomial inner (1 - value)) := by
      rw [crossPolynomial_eq_one_sub_spreadPolynomial inner value]
      congr 2
      ring1
    _ = 1 - spreadPolynomial (outer * inner) (1 - value) := by
      rw [spread_polynomial_composition]
    _ = crossPolynomial (outer * inner) value :=
      (crossPolynomial_eq_one_sub_spreadPolynomial (outer * inner) value).symm

/-- Exercise 8.17 in the source's two-variable form. -/
theorem exercise_8_17
    (index : Nat) (crossValue spreadValue : K)
    (complementary : crossValue + spreadValue = 1) :
    crossPolynomial index crossValue +
      spreadPolynomial index spreadValue = 1 := by
  have spreadValueEquation : spreadValue = 1 - crossValue := by
    calc
      spreadValue = (crossValue + spreadValue) - crossValue := by ring1
      _ = 1 - crossValue := by rw [complementary]
  rw [crossPolynomial_eq_one_sub_spreadPolynomial, spreadValueEquation]
  ring1

/-- The even and odd clauses of Exercise 8.18, proved together by finite
induction. -/
theorem crossPolynomial_even_and_odd (index : Nat) (value : K) :
    crossPolynomial (index + index) value =
        1 - spreadPolynomial (index + index) value ∧
      crossPolynomial (index + index + 1) value =
        spreadPolynomial (index + index + 1) value := by
  induction index with
  | zero =>
      constructor <;> unfold crossPolynomial spreadPolynomial <;> ring1
  | succ index inductionHypothesis =>
      rcases inductionHypothesis with ⟨evenFormula, oddFormula⟩
      have nextEven :
          crossPolynomial (Nat.succ index + Nat.succ index) value =
            1 - spreadPolynomial (Nat.succ index + Nat.succ index) value := by
        rw [show Nat.succ index + Nat.succ index = index + index + 2 by omega0]
        rw [crossPolynomial_succ_succ, spreadPolynomial_succ_succ,
          evenFormula, oddFormula]
        ring1
      have nextOdd :
          crossPolynomial (Nat.succ index + Nat.succ index + 1) value =
            spreadPolynomial (Nat.succ index + Nat.succ index + 1) value := by
        rw [show Nat.succ index + Nat.succ index + 1 =
          (index + index + 1) + 2 by omega0]
        rw [crossPolynomial_succ_succ, spreadPolynomial_succ_succ,
          oddFormula]
        rw [show index + index + 2 =
          Nat.succ index + Nat.succ index by omega0]
        rw [nextEven]
        ring1
      exact ⟨nextEven, nextOdd⟩

/-- Exercise 8.19's first doubling identity. -/
theorem exercise_8_19_cross
    (index : Nat) (value : K) :
    (crossPolynomial index value -
        spreadPolynomial index (1 - value)) ^ 2 =
      crossPolynomial (2 * index) value := by
  have complement := crossPolynomial_eq_one_sub_spreadPolynomial index value
  calc
    (crossPolynomial index value -
          spreadPolynomial index (1 - value)) ^ 2 =
        (2 * crossPolynomial index value - 1) ^ 2 := by rw [complement]; ring1
    _ = crossPolynomial 2 (crossPolynomial index value) := by
      symm
      change
        2 * (2 * crossPolynomial index value - 1) *
              crossPolynomial 1 (crossPolynomial index value) -
            crossPolynomial 0 (crossPolynomial index value) +
            2 * (1 - crossPolynomial index value) =
          (2 * crossPolynomial index value - 1) ^ 2
      rw [crossPolynomial_zero, crossPolynomial_one]
      ring1
    _ = crossPolynomial (2 * index) value :=
      cross_polynomial_composition 2 index value

/-- Exercise 8.19's second doubling identity. -/
theorem exercise_8_19_spread
    (index : Nat) (value : K) :
    4 * spreadPolynomial index value *
        crossPolynomial index (1 - value) =
      spreadPolynomial (2 * index) value := by
  have crossComplement :
      crossPolynomial index (1 - value) =
        1 - spreadPolynomial index value := by
    calc
      crossPolynomial index (1 - value) =
          1 - spreadPolynomial index (1 - (1 - value)) :=
        crossPolynomial_eq_one_sub_spreadPolynomial index (1 - value)
      _ = 1 - spreadPolynomial index value := by
        congr 2
        ring1
  rw [crossComplement]
  calc
    4 * spreadPolynomial index value *
          (1 - spreadPolynomial index value) =
        spreadPolynomial 2 (spreadPolynomial index value) := by
      change
        4 * spreadPolynomial index value *
            (1 - spreadPolynomial index value) =
          2 * (1 - 2 * spreadPolynomial index value) *
              spreadPolynomial 1 (spreadPolynomial index value) -
            spreadPolynomial 0 (spreadPolynomial index value) +
            2 * spreadPolynomial index value
      rw [spreadPolynomial_zero, spreadPolynomial_one]
      ring1
    _ = spreadPolynomial (2 * index) value :=
      spread_polynomial_composition 2 index value

end DivineProportions
