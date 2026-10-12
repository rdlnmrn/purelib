module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
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
# Divine Proportions, remaining Chapter 8 exercises

This module records the finite algebra behind Exercises 8.2, 8.5, and
8.11--8.13.  Exercise 8.5 is proved uniformly for arbitrary natural residue
labels in characteristic `p`, using a finite prime-binomial argument rather
than an enumeration of an ambient field carrier.  Exercise 8.2 is likewise
proved for arbitrary residue labels using an executable quadratic pair and a
finite decidable algebraic split.  Exercise 8.11's bounded-sum interface is
defined here; its uniform prime-residue arithmetic and complete inner-product
results are proved in `ChapterEightInnerProduct`.

Exercise 8.12 is deliberately stopped before its completed-real integral.
The exact polynomial numerator obtained from the Chebyshev substitution is
proved for every requested pair of finite indices.  Exercise 8.13's printed
spread-cyclotomic factors are retained as explicit integer-coefficient
expressions, and every displayed divisor product is checked directly.  Its
finite totient and Lucas-square reduction is developed in
`SpreadCyclotomicReduction`; the arbitrary-index constructive factorization
and exact totient-degree theorem are completed in
`SpreadCyclotomicFactorization`.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Chebyshev.Product

variable {K : Type*} [ExplicitField K]

section

/-- A product of centered spread values equals a product of translated Chebyshev values.

The identity is denominator-free and holds at every pair of natural indices over the supplied explicit field. -/
theorem centered_product_cleared
    (firstIndex secondIndex : Nat) (value : K) :
    (2 * Recurrence.Spread.Basic.spreadPolynomial firstIndex value - 1) *
        (2 * Recurrence.Spread.Basic.spreadPolynomial secondIndex value - 1) =
      Recurrence.Chebyshev.First.Basic.chebyshevFirst firstIndex (1 - 2 * value) *
        Recurrence.Chebyshev.First.Basic.chebyshevFirst secondIndex (1 - 2 * value) := by
  rw [Recurrence.Spread.Chebyshev.exercise_8_4_cleared firstIndex value,
    Recurrence.Spread.Chebyshev.exercise_8_4_cleared secondIndex value]
  ring1

/-- Four times the product of spread values centered at one half equals a Chebyshev product.

The coefficient field must have nonzero two to interpret and cancel the half shifts. -/
theorem centered_product
    (firstIndex secondIndex : Nat) (value : K)
    (twoNonzero : (2 : K) ≠ 0) :
    4 *
        (Recurrence.Spread.Basic.spreadPolynomial firstIndex value - 1 / 2) *
        (Recurrence.Spread.Basic.spreadPolynomial secondIndex value - 1 / 2) =
      Recurrence.Chebyshev.First.Basic.chebyshevFirst firstIndex (1 - 2 * value) *
        Recurrence.Chebyshev.First.Basic.chebyshevFirst secondIndex (1 - 2 * value) := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  have firstCentered :
      2 * (Recurrence.Spread.Basic.spreadPolynomial firstIndex value - 1 / 2) =
        2 * Recurrence.Spread.Basic.spreadPolynomial firstIndex value - 1 := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      2 * (Recurrence.Spread.Basic.spreadPolynomial firstIndex value - 1 * (2 : K)⁻¹) =
          2 * Recurrence.Spread.Basic.spreadPolynomial firstIndex value -
            (2 : K) * (2 : K)⁻¹ := by ring1
      _ = 2 * Recurrence.Spread.Basic.spreadPolynomial firstIndex value - 1 := by rw [twoCancel]
  have secondCentered :
      2 * (Recurrence.Spread.Basic.spreadPolynomial secondIndex value - 1 / 2) =
        2 * Recurrence.Spread.Basic.spreadPolynomial secondIndex value - 1 := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      2 * (Recurrence.Spread.Basic.spreadPolynomial secondIndex value - 1 * (2 : K)⁻¹) =
          2 * Recurrence.Spread.Basic.spreadPolynomial secondIndex value -
            (2 : K) * (2 : K)⁻¹ := by ring1
      _ = 2 * Recurrence.Spread.Basic.spreadPolynomial secondIndex value - 1 := by rw [twoCancel]
  calc
    4 * (Recurrence.Spread.Basic.spreadPolynomial firstIndex value - 1 / 2) *
          (Recurrence.Spread.Basic.spreadPolynomial secondIndex value - 1 / 2) =
        (2 * (Recurrence.Spread.Basic.spreadPolynomial firstIndex value - 1 / 2)) *
          (2 * (Recurrence.Spread.Basic.spreadPolynomial secondIndex value - 1 / 2)) := by ring1
    _ = (2 * Recurrence.Spread.Basic.spreadPolynomial firstIndex value - 1) *
          (2 * Recurrence.Spread.Basic.spreadPolynomial secondIndex value - 1) := by
      rw [firstCentered, secondCentered]
    _ = Recurrence.Chebyshev.First.Basic.chebyshevFirst firstIndex (1 - 2 * value) *
          Recurrence.Chebyshev.First.Basic.chebyshevFirst secondIndex (1 - 2 * value) :=
      centered_product_cleared firstIndex secondIndex value

end

end Purelib.Polynomial.Recurrence.Spread.Chebyshev.Product

end
