module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
public import Purelib.Polynomial.Recurrence.Lucas.Basic
import Purelib.Polynomial.Recurrence.Lucas.Chebyshev
import Purelib.Polynomial.Recurrence.Lucas.Identities
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Chebyshev

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite Lucas reduction for spread-cyclotomic factorization

Exercise 8.13 was the Goh--Wildberger factorization conjecture; a proof only
appeared in Cigler--Herbig (2026).  This module isolates the entirely finite
algebraic part of that proof.  Lucas values are primitive recursion, their
product and square identities come from the finite Chebyshev recurrence, and
Euler's totient is the bounded count in `Purelib.NumberTheory.Totient`.

No roots, cosine values, completed fields, or infinite polynomial family are
introduced here.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Lucas.ExerciseEightThirteen

variable {K : Type*} [ExplicitField K]

section

/-- The source's spread/Lucas formula in denominator-free form. -/
theorem spread_lucas_cleared (index : Nat)
  (value : K) :
    4 * Recurrence.Spread.Basic.spreadPolynomial index value =
      2 - Recurrence.Lucas.Basic.lucas index (2 - 4 * value) := by
  have centered := Recurrence.Spread.Chebyshev.exercise_8_4_cleared index value
  rw [show 2 - 4 * value = 2 * (1 - 2 * value) by ring1,
    Recurrence.Lucas.Chebyshev.ExerciseEightThirteen.lucas_at_double]
  calc
    4 * Recurrence.Spread.Basic.spreadPolynomial index value =
        2 * (2 * Recurrence.Spread.Basic.spreadPolynomial index value) := by ring1
    _ = 2 * (1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst index (1 - 2 * value)) := by
      rw [centered]
    _ = 2 - 2 * Recurrence.Chebyshev.First.Basic.chebyshevFirst index (1 - 2 * value) := by ring1

/-- Odd spread polynomials inherit the Lucas square factorization, with all
factors cleared in the coefficient field. -/
theorem spread_odd_lucas_square_cleared
    (half : Nat) (value : K) :
    16 * value * Recurrence.Spread.Basic.spreadPolynomial (half + half + 1) value =
      (Recurrence.Lucas.Basic.lucas (half + 1) (2 - 4 * value) -
        Recurrence.Lucas.Basic.lucas half (2 - 4 * value)) ^ 2 := by
  have lucasSquare := Recurrence.Lucas.Identities.ExerciseEightThirteen.lucas_odd_square_identity
    (K := K) half (1 - 2 * value)
  rw [show 2 * (1 - 2 * value) = 2 - 4 * value by ring1]
    at lucasSquare
  have spreadIdentity := spread_lucas_cleared
    (K := K) (half + half + 1) value
  have lucasDifference :
      Recurrence.Lucas.Basic.lucas (half + half + 1) (2 - 4 * value) - 2 =
        -4 * Recurrence.Spread.Basic.spreadPolynomial (half + half + 1) value := by
    calc
      Recurrence.Lucas.Basic.lucas (half + half + 1) (2 - 4 * value) - 2 =
          -(2 - Recurrence.Lucas.Basic.lucas (half + half + 1) (2 - 4 * value)) := by
            ring1
      _ = -(4 * Recurrence.Spread.Basic.spreadPolynomial (half + half + 1) value) := by
        rw [← spreadIdentity]
      _ = -4 * Recurrence.Spread.Basic.spreadPolynomial (half + half + 1) value := by ring1
  calc
    16 * value * Recurrence.Spread.Basic.spreadPolynomial (half + half + 1) value =
      (Recurrence.Lucas.Basic.lucas (half + half + 1) (2 - 4 * value) - 2) *
        ((2 - 4 * value) - 2) := by
          rw [lucasDifference]
          ring1
    _ = (Recurrence.Lucas.Basic.lucas (half + 1) (2 - 4 * value) -
        Recurrence.Lucas.Basic.lucas half (2 - 4 * value)) ^ 2 := lucasSquare

/-- Even spread polynomials likewise carry the two simple endpoint factors
and a square remainder, again without division. -/
theorem spread_even_lucas_square_cleared
    (half : Nat) (halfPositive : 1 ≤ half) (value : K) :
    64 * value * (1 - value) *
        Recurrence.Spread.Basic.spreadPolynomial (half + half) value =
      (Recurrence.Lucas.Basic.lucas (half + 1) (2 - 4 * value) -
        Recurrence.Lucas.Basic.lucas (half - 1) (2 - 4 * value)) ^ 2 := by
  have lucasSquare := Recurrence.Lucas.Identities.ExerciseEightThirteen.lucas_even_square_identity
    (K := K) half halfPositive (1 - 2 * value)
  rw [show 2 * (1 - 2 * value) = 2 - 4 * value by ring1]
    at lucasSquare
  have spreadIdentity := spread_lucas_cleared
    (K := K) (half + half) value
  have lucasDifference :
      Recurrence.Lucas.Basic.lucas (half + half) (2 - 4 * value) - 2 =
        -4 * Recurrence.Spread.Basic.spreadPolynomial (half + half) value := by
    calc
      Recurrence.Lucas.Basic.lucas (half + half) (2 - 4 * value) - 2 =
          -(2 - Recurrence.Lucas.Basic.lucas (half + half) (2 - 4 * value)) := by ring1
      _ = -(4 * Recurrence.Spread.Basic.spreadPolynomial (half + half) value) := by
        rw [← spreadIdentity]
      _ = -4 * Recurrence.Spread.Basic.spreadPolynomial (half + half) value := by ring1
  calc
    64 * value * (1 - value) *
        Recurrence.Spread.Basic.spreadPolynomial (half + half) value =
      (Recurrence.Lucas.Basic.lucas (half + half) (2 - 4 * value) - 2) *
        (((2 - 4 * value) - 2) * ((2 - 4 * value) + 2)) := by
          rw [lucasDifference]
          ring1
    _ = (Recurrence.Lucas.Basic.lucas (half + 1) (2 - 4 * value) -
        Recurrence.Lucas.Basic.lucas (half - 1) (2 - 4 * value)) ^ 2 := lucasSquare

end

end Purelib.Polynomial.Recurrence.Spread.Lucas.ExerciseEightThirteen

end
