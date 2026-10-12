module
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Composition

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Cross.Basic
import Purelib.Polynomial.Recurrence.Cross.Composition
import Purelib.Polynomial.Recurrence.Cross.Spread
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

namespace Purelib.Polynomial.Recurrence.Cross.Doubling

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- The squared difference of complementary cross and spread values equals the cross polynomial at twice the index. -/
theorem exercise_8_19_cross
    (index : Nat) (value : K) :
    (Recurrence.Cross.Basic.crossPolynomial index value -
        Recurrence.Spread.Basic.spreadPolynomial index (1 - value)) ^ 2 =
      Recurrence.Cross.Basic.crossPolynomial (2 * index) value := by
  have complement := Recurrence.Cross.Spread.crossPolynomial_eq_one_sub_spreadPolynomial index value
  calc
    (Recurrence.Cross.Basic.crossPolynomial index value -
          Recurrence.Spread.Basic.spreadPolynomial index (1 - value)) ^ 2 =
        (2 * Recurrence.Cross.Basic.crossPolynomial index value - 1) ^ 2 := by rw [complement]; ring1
    _ = Recurrence.Cross.Basic.crossPolynomial 2 (Recurrence.Cross.Basic.crossPolynomial index value) := by
      symm
      change
        2 * (2 * Recurrence.Cross.Basic.crossPolynomial index value - 1) *
              Recurrence.Cross.Basic.crossPolynomial 1 (Recurrence.Cross.Basic.crossPolynomial index value) -
            Recurrence.Cross.Basic.crossPolynomial 0 (Recurrence.Cross.Basic.crossPolynomial index value) +
            2 * (1 - Recurrence.Cross.Basic.crossPolynomial index value) =
          (2 * Recurrence.Cross.Basic.crossPolynomial index value - 1) ^ 2
      rw [Recurrence.Cross.Basic.crossPolynomial_zero, Recurrence.Cross.Basic.crossPolynomial_one]
      ring1
    _ = Recurrence.Cross.Basic.crossPolynomial (2 * index) value :=
      Recurrence.Cross.Composition.cross_polynomial_composition 2 index value

/-- Four times a spread value times its complementary cross value equals the spread polynomial at twice the index. -/
theorem exercise_8_19_spread
    (index : Nat) (value : K) :
    4 * Recurrence.Spread.Basic.spreadPolynomial index value *
        Recurrence.Cross.Basic.crossPolynomial index (1 - value) =
      Recurrence.Spread.Basic.spreadPolynomial (2 * index) value := by
  have crossComplement :
      Recurrence.Cross.Basic.crossPolynomial index (1 - value) =
        1 - Recurrence.Spread.Basic.spreadPolynomial index value := by
    calc
      Recurrence.Cross.Basic.crossPolynomial index (1 - value) =
          1 - Recurrence.Spread.Basic.spreadPolynomial index (1 - (1 - value)) :=
        Recurrence.Cross.Spread.crossPolynomial_eq_one_sub_spreadPolynomial index (1 - value)
      _ = 1 - Recurrence.Spread.Basic.spreadPolynomial index value := by
        congr 2
        ring1
  rw [crossComplement]
  calc
    4 * Recurrence.Spread.Basic.spreadPolynomial index value *
          (1 - Recurrence.Spread.Basic.spreadPolynomial index value) =
        Recurrence.Spread.Basic.spreadPolynomial 2 (Recurrence.Spread.Basic.spreadPolynomial index value) := by
      change
        4 * Recurrence.Spread.Basic.spreadPolynomial index value *
            (1 - Recurrence.Spread.Basic.spreadPolynomial index value) =
          2 * (1 - 2 * Recurrence.Spread.Basic.spreadPolynomial index value) *
              Recurrence.Spread.Basic.spreadPolynomial 1 (Recurrence.Spread.Basic.spreadPolynomial index value) -
            Recurrence.Spread.Basic.spreadPolynomial 0 (Recurrence.Spread.Basic.spreadPolynomial index value) +
            2 * Recurrence.Spread.Basic.spreadPolynomial index value
      rw [Recurrence.Spread.Basic.spreadPolynomial_zero, Recurrence.Spread.Basic.spreadPolynomial_one]
      ring1
    _ = Recurrence.Spread.Basic.spreadPolynomial (2 * index) value :=
      Recurrence.Spread.Composition.spread_polynomial_composition 2 index value

end Purelib.Polynomial.Recurrence.Cross.Doubling

end
