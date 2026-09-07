import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadPolynomial

/-!
# Divine Proportions, Chapter 8: the finite Chebyshev identity

Only the polynomial recurrence in Exercise 8.4 is retained.  The source's
alternative notation using a square root in a completed decimal field is not
needed for, and adds no content to, this exact identity.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The Chebyshev polynomial of the first kind, as a primitive-recursive
finite field expression. -/
def chebyshevFirst : Nat → K → K
  | 0, _ => 1
  | 1, value => value
  | index + 2, value =>
      2 * value * chebyshevFirst (index + 1) value -
        chebyshevFirst index value

@[simp] theorem chebyshevFirst_zero (value : K) :
    chebyshevFirst 0 value = 1 := rfl

@[simp] theorem chebyshevFirst_one (value : K) :
    chebyshevFirst 1 value = value := rfl

@[simp] theorem chebyshevFirst_succ_succ (index : Nat) (value : K) :
    chebyshevFirst (index + 2) value =
      2 * value * chebyshevFirst (index + 1) value -
        chebyshevFirst index value := rfl

/-- Product-to-sum in subtraction-free natural coordinates:
`2T_(a+b)T_b = T_(a+2b)+T_a`. -/
theorem chebyshevFirst_product_add_sub :
    ∀ offset step : Nat, ∀ value : K,
      2 * chebyshevFirst (offset + step) value *
          chebyshevFirst step value =
        chebyshevFirst (offset + step + step) value +
          chebyshevFirst offset value
  | offset, 0, value => by
      simp only [Nat.add_zero, chebyshevFirst_zero]
      ring1
  | offset, 1, value => by
      rw [show offset + 1 + 1 = offset + 2 by omega0,
        chebyshevFirst_succ_succ, chebyshevFirst_one]
      ring1
  | offset, step + 2, value => by
      have previous := chebyshevFirst_product_add_sub
        (offset + 1) (step + 1) value
      have beforePrevious := chebyshevFirst_product_add_sub
        (offset + 2) step value
      rw [show offset + 1 + (step + 1) =
          offset + step + 2 by omega0] at previous
      rw [show offset + 2 + step =
          offset + step + 2 by omega0] at beforePrevious
      have upperRecurrence :
          2 * value *
                chebyshevFirst
                  (offset + step + 2 + (step + 1)) value -
              chebyshevFirst (offset + step + 2 + step) value =
            chebyshevFirst
              (offset + (step + 2) + (step + 2)) value := by
        rw [show offset + step + 2 + (step + 1) =
            (offset + step + 2 + step) + 1 by omega0,
          ← chebyshevFirst_succ_succ]
        congr 1
      have lowerRecurrence :
          2 * value * chebyshevFirst (offset + 1) value -
              chebyshevFirst (offset + 2) value =
            chebyshevFirst offset value := by
        rw [chebyshevFirst_succ_succ]
        ring1
      rw [show offset + (step + 2) = offset + step + 2 by omega0]
      rw [chebyshevFirst_succ_succ]
      calc
        2 * chebyshevFirst (offset + step + 2) value *
            (2 * value * chebyshevFirst (step + 1) value -
              chebyshevFirst step value) =
          2 * value *
              (2 * chebyshevFirst (offset + step + 2) value *
                chebyshevFirst (step + 1) value) -
            (2 * chebyshevFirst (offset + step + 2) value *
              chebyshevFirst step value) := by ring1
        _ = 2 * value *
              (chebyshevFirst (offset + step + 2 + (step + 1)) value +
                chebyshevFirst (offset + 1) value) -
            (chebyshevFirst (offset + step + 2 + step) value +
              chebyshevFirst (offset + 2) value) := by
                rw [previous, beforePrevious]
        _ = chebyshevFirst (offset + (step + 2) + (step + 2)) value +
              chebyshevFirst offset value := by
                rw [show 2 * value *
                      (chebyshevFirst
                          (offset + step + 2 + (step + 1)) value +
                        chebyshevFirst (offset + 1) value) -
                      (chebyshevFirst
                          (offset + step + 2 + step) value +
                        chebyshevFirst (offset + 2) value) =
                    (2 * value * chebyshevFirst
                        (offset + step + 2 + (step + 1)) value -
                      chebyshevFirst (offset + step + 2 + step) value) +
                    (2 * value * chebyshevFirst (offset + 1) value -
                      chebyshevFirst (offset + 2) value) by ring1]
                rw [upperRecurrence, lowerRecurrence]

/-- Exercise 8.4 in denominator-free form. -/
theorem exercise_8_4_cleared (index : Nat) (value : K) :
    2 * spreadPolynomial index value =
      1 - chebyshevFirst index (1 - 2 * value) := by
  let identityAt := fun current : Nat =>
    2 * spreadPolynomial current value =
      1 - chebyshevFirst current (1 - 2 * value)
  have allPairs : ∀ current : Nat,
      identityAt current ∧ identityAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · unfold identityAt spreadPolynomial chebyshevFirst
          ring1
        · unfold identityAt spreadPolynomial chebyshevFirst
          ring1
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · unfold identityAt
          rw [show Nat.succ current + 1 = current + 2 by omega0]
          rw [spreadPolynomial_succ_succ, chebyshevFirst_succ_succ]
          calc
            2 *
                (2 * (1 - 2 * value) *
                    spreadPolynomial (current + 1) value -
                  spreadPolynomial current value + 2 * value) =
              2 * (1 - 2 * value) *
                  (2 * spreadPolynomial (current + 1) value) -
                2 * spreadPolynomial current value + 4 * value := by ring1
            _ = 2 * (1 - 2 * value) *
                  (1 - chebyshevFirst (current + 1) (1 - 2 * value)) -
                (1 - chebyshevFirst current (1 - 2 * value)) +
                4 * value := by
              rw [inductionHypothesis.1, inductionHypothesis.2]
            _ = 1 -
                (2 * (1 - 2 * value) *
                    chebyshevFirst (current + 1) (1 - 2 * value) -
                  chebyshevFirst current (1 - 2 * value)) := by ring1
  exact (allPairs index).1

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

/-- Exercise 8.4's quotient form, with characteristic two excluded exactly
where the displayed division requires it. -/
theorem exercise_8_4
    (index : Nat) (value : K) (twoNonzero : (2 : K) ≠ 0) :
    spreadPolynomial index value =
      (1 - chebyshevFirst index (1 - 2 * value)) / 2 := by
  apply eq_of_mul_eq_mul_right twoNonzero
  calc
    spreadPolynomial index value * 2 =
        2 * spreadPolynomial index value := by ring1
    _ = 1 - chebyshevFirst index (1 - 2 * value) :=
      exercise_8_4_cleared index value
    _ = ((1 - chebyshevFirst index (1 - 2 * value)) / 2) * 2 :=
      (RFAP.ExplicitField.div_mul_cancel _ twoNonzero).symm

end DivineProportions
