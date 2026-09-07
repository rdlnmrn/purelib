import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.SpreadPolynomial

/-!
# Divine Proportions, Chapter 8 worked examples

The displayed formulas are finite polynomial identities over an arbitrary
constructive explicit field.  In particular, they may be evaluated over the
project's constructive rationals or any of its explicit finite fields.
-/

namespace DivineProportions

namespace ChapterEightExamples

variable {K : Type*} [RFAP.ExplicitField K]

/-- The quadratic spread polynomial in both displayed forms. -/
theorem spreadPolynomial_two (value : K) :
    spreadPolynomial 2 value = 4 * value - 4 * value ^ 2 ∧
      spreadPolynomial 2 value = 4 * value * (1 - value) := by
  simp only [spreadPolynomial]
  exact ⟨by ring1, by ring1⟩

/-- The cubic spread polynomial used in Example 8.5. -/
theorem spreadPolynomial_three (value : K) :
    spreadPolynomial 3 value = value * (3 - 4 * value) ^ 2 := by
  simp only [spreadPolynomial]
  ring1

theorem spreadPolynomial_three_expanded (value : K) :
    spreadPolynomial 3 value =
      9 * value - 24 * value ^ 2 + 16 * value ^ 3 := by
  rw [spreadPolynomial_three]
  ring1

/-- The quartic spread polynomial in both displayed forms. -/
theorem spreadPolynomial_four (value : K) :
    spreadPolynomial 4 value =
        16 * value - 80 * value ^ 2 + 128 * value ^ 3 - 64 * value ^ 4 ∧
      spreadPolynomial 4 value =
        16 * value * (1 - value) * (1 - 2 * value) ^ 2 := by
  simp only [spreadPolynomial]
  exact ⟨by ring1, by ring1⟩

/-- The quintic spread polynomial used in Example 8.5. -/
theorem spreadPolynomial_five (value : K) :
    spreadPolynomial 5 value =
      value * (5 - 20 * value + 16 * value ^ 2) ^ 2 := by
  simp only [spreadPolynomial]
  ring1

theorem spreadPolynomial_five_expanded (value : K) :
    spreadPolynomial 5 value =
      25 * value - 200 * value ^ 2 + 560 * value ^ 3 -
        640 * value ^ 4 + 256 * value ^ 5 := by
  rw [spreadPolynomial_five]
  ring1

/-- The sextic spread polynomial in both displayed forms. -/
theorem spreadPolynomial_six (value : K) :
    spreadPolynomial 6 value =
        36 * value - 420 * value ^ 2 + 1792 * value ^ 3 -
          3456 * value ^ 4 + 3072 * value ^ 5 - 1024 * value ^ 6 ∧
      spreadPolynomial 6 value =
        4 * value * (1 - value) * (1 - 4 * value) ^ 2 *
          (3 - 4 * value) ^ 2 := by
  simp only [spreadPolynomial]
  exact ⟨by ring1, by ring1⟩

/-- The seventh spread polynomial in both displayed forms. -/
theorem spreadPolynomial_seven (value : K) :
    spreadPolynomial 7 value =
        49 * value - 784 * value ^ 2 + 4704 * value ^ 3 -
          13440 * value ^ 4 + 19712 * value ^ 5 -
          14336 * value ^ 6 + 4096 * value ^ 7 ∧
      spreadPolynomial 7 value =
        value * (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 := by
  simp only [spreadPolynomial]
  exact ⟨by ring1, by ring1⟩

/-- Example 8.5's first computation of `S₁₅` as `S₃(S₅(s))`. -/
theorem example_8_5_fifteen_composition (value : K) :
    spreadPolynomial 15 value =
      value * (5 - 20 * value + 16 * value ^ 2) ^ 2 *
        (3 - 4 * value *
          (5 - 20 * value + 16 * value ^ 2) ^ 2) ^ 2 := by
  calc
    spreadPolynomial 15 value =
        spreadPolynomial 3 (spreadPolynomial 5 value) :=
      (spread_polynomial_composition 3 5 value).symm
    _ = spreadPolynomial 5 value *
        (3 - 4 * spreadPolynomial 5 value) ^ 2 :=
      spreadPolynomial_three _
    _ = value * (5 - 20 * value + 16 * value ^ 2) ^ 2 *
        (3 - 4 * value *
          (5 - 20 * value + 16 * value ^ 2) ^ 2) ^ 2 := by
      rw [spreadPolynomial_five]
      ring1

/-- The fully factored `S₁₅` formula displayed in Example 8.5. -/
theorem example_8_5_fifteen_factored (value : K) :
    spreadPolynomial 15 value =
      value * (3 - 4 * value) ^ 2 *
        (5 - 20 * value + 16 * value ^ 2) ^ 2 *
        (1 - 32 * value + 224 * value ^ 2 - 448 * value ^ 3 +
          256 * value ^ 4) ^ 2 := by
  rw [example_8_5_fifteen_composition]
  ring1

/-- Example 8.5's finite `S₃₀ = S₂(S₁₅)` step. -/
theorem example_8_5_thirty_composition (value : K) :
    spreadPolynomial 30 value =
      4 * spreadPolynomial 15 value *
        (1 - spreadPolynomial 15 value) := by
  calc
    spreadPolynomial 30 value =
        spreadPolynomial 2 (spreadPolynomial 15 value) :=
      (spread_polynomial_composition 2 15 value).symm
    _ = 4 * spreadPolynomial 15 value *
        (1 - spreadPolynomial 15 value) := by
      simp only [spreadPolynomial]
      ring1

/-- The fully factored `S₃₀` formula displayed in Example 8.5. -/
theorem example_8_5_thirty_factored (value : K) :
    spreadPolynomial 30 value =
      4 * value * (1 - value) * (3 - 4 * value) ^ 2 *
        (5 - 20 * value + 16 * value ^ 2) ^ 2 *
        (1 - 32 * value + 224 * value ^ 2 - 448 * value ^ 3 +
          256 * value ^ 4) ^ 2 *
        (1 - 4 * value) ^ 2 *
        (1 - 12 * value + 16 * value ^ 2) ^ 2 *
        (1 - 96 * value + 416 * value ^ 2 - 576 * value ^ 3 +
          256 * value ^ 4) ^ 2 := by
  rw [example_8_5_thirty_composition,
    example_8_5_fifteen_factored]
  ring1

end ChapterEightExamples

end DivineProportions
