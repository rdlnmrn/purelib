module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Cross.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: cross polynomials

The cross-polynomial exercises are proved from their primitive recursion and
the already finite spread-polynomial recurrence.  Every index requests only a
bounded number of arithmetic steps.
-/

namespace Purelib.Polynomial.Recurrence.Cross.Values

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- Explicit cross-polynomial values through index six.

The conjunction records both expanded and factored forms over the supplied explicit field. -/
theorem exercise_8_15 (value : K) :
    Recurrence.Cross.Basic.crossPolynomial 0 value = 1 ∧
      Recurrence.Cross.Basic.crossPolynomial 1 value = value ∧
      Recurrence.Cross.Basic.crossPolynomial 2 value = 1 - 4 * value + 4 * value ^ 2 ∧
      Recurrence.Cross.Basic.crossPolynomial 2 value = (1 - 2 * value) ^ 2 ∧
      Recurrence.Cross.Basic.crossPolynomial 3 value =
        9 * value - 24 * value ^ 2 + 16 * value ^ 3 ∧
      Recurrence.Cross.Basic.crossPolynomial 3 value = value * (3 - 4 * value) ^ 2 ∧
      Recurrence.Cross.Basic.crossPolynomial 4 value =
        1 - 16 * value + 80 * value ^ 2 - 128 * value ^ 3 +
          64 * value ^ 4 ∧
      Recurrence.Cross.Basic.crossPolynomial 4 value = (1 - 8 * value + 8 * value ^ 2) ^ 2 ∧
      Recurrence.Cross.Basic.crossPolynomial 5 value =
        value * (5 - 20 * value + 16 * value ^ 2) ^ 2 ∧
      Recurrence.Cross.Basic.crossPolynomial 6 value =
        (1 - 2 * value) ^ 2 * (1 - 16 * value + 16 * value ^ 2) ^ 2 := by
  have valueTwo : Recurrence.Cross.Basic.crossPolynomial 2 value =
      1 - 4 * value + 4 * value ^ 2 := by
    change
      2 * (2 * value - 1) * Recurrence.Cross.Basic.crossPolynomial 1 value -
          Recurrence.Cross.Basic.crossPolynomial 0 value + 2 * (1 - value) =
        1 - 4 * value + 4 * value ^ 2
    rw [Recurrence.Cross.Basic.crossPolynomial_zero, Recurrence.Cross.Basic.crossPolynomial_one]
    ring1
  have valueThree : Recurrence.Cross.Basic.crossPolynomial 3 value =
      9 * value - 24 * value ^ 2 + 16 * value ^ 3 := by
    change
      2 * (2 * value - 1) * Recurrence.Cross.Basic.crossPolynomial 2 value -
          Recurrence.Cross.Basic.crossPolynomial 1 value + 2 * (1 - value) =
        9 * value - 24 * value ^ 2 + 16 * value ^ 3
    rw [valueTwo, Recurrence.Cross.Basic.crossPolynomial_one]
    ring1
  have valueFour : Recurrence.Cross.Basic.crossPolynomial 4 value =
      1 - 16 * value + 80 * value ^ 2 - 128 * value ^ 3 +
        64 * value ^ 4 := by
    change
      2 * (2 * value - 1) * Recurrence.Cross.Basic.crossPolynomial 3 value -
          Recurrence.Cross.Basic.crossPolynomial 2 value + 2 * (1 - value) =
        1 - 16 * value + 80 * value ^ 2 - 128 * value ^ 3 +
          64 * value ^ 4
    rw [valueThree, valueTwo]
    ring1
  have valueFive : Recurrence.Cross.Basic.crossPolynomial 5 value =
      value * (5 - 20 * value + 16 * value ^ 2) ^ 2 := by
    change
      2 * (2 * value - 1) * Recurrence.Cross.Basic.crossPolynomial 4 value -
          Recurrence.Cross.Basic.crossPolynomial 3 value + 2 * (1 - value) =
        value * (5 - 20 * value + 16 * value ^ 2) ^ 2
    rw [valueFour, valueThree]
    ring1
  have valueSix : Recurrence.Cross.Basic.crossPolynomial 6 value =
      (1 - 2 * value) ^ 2 *
        (1 - 16 * value + 16 * value ^ 2) ^ 2 := by
    change
      2 * (2 * value - 1) * Recurrence.Cross.Basic.crossPolynomial 5 value -
          Recurrence.Cross.Basic.crossPolynomial 4 value + 2 * (1 - value) =
        (1 - 2 * value) ^ 2 *
          (1 - 16 * value + 16 * value ^ 2) ^ 2
    rw [valueFive, valueFour]
    ring1
  exact ⟨Recurrence.Cross.Basic.crossPolynomial_zero value, Recurrence.Cross.Basic.crossPolynomial_one value,
    valueTwo, valueTwo.trans (by ring1), valueThree,
    valueThree.trans (by ring1), valueFour, valueFour.trans (by ring1),
    valueFive, valueSix⟩
end Purelib.Polynomial.Recurrence.Cross.Values

end
