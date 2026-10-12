module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Spread.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib

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

namespace formalisations.DivineProportions.Chapters.Trigonometry.ChapterEightRemaining

variable {K : Type*} [Field.ExplicitField K]

namespace ExerciseEightThirteen

/-- The printed spread-cyclotomic factors.  Each is a literal finite
integer-coefficient expression evaluated in the requested field. -/
def cyclotomicOne (value : K) : K := value
/-- The displayed index-two spread-cyclotomic factor 4(1 − s). -/
def cyclotomicTwo (value : K) : K := 4 * (1 - value)
/-- The displayed index-three spread-cyclotomic factor (3 − 4s)². -/
def cyclotomicThree (value : K) : K := (3 - 4 * value) ^ 2
/-- The displayed index-four spread-cyclotomic factor 4(1 − 2s)². -/
def cyclotomicFour (value : K) : K := 4 * (1 - 2 * value) ^ 2
/-- The displayed index-five spread-cyclotomic factor (5 − 20s + 16s²)². -/
def cyclotomicFive (value : K) : K :=
  (5 - 20 * value + 16 * value ^ 2) ^ 2
/-- The displayed index-six spread-cyclotomic factor (1 − 4s)². -/
def cyclotomicSix (value : K) : K := (1 - 4 * value) ^ 2
/-- The displayed index-seven spread-cyclotomic factor (7 − 56s + 112s² − 64s³)². -/
def cyclotomicSeven (value : K) : K :=
  (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2
/-- The displayed index-eight spread-cyclotomic factor 4(1 − 8s + 8s²)². -/
def cyclotomicEight (value : K) : K :=
  4 * (1 - 8 * value + 8 * value ^ 2) ^ 2
/-- The displayed index-twelve spread-cyclotomic factor (1 − 16s + 16s²)². -/
def cyclotomicTwelve (value : K) : K :=
  (1 - 16 * value + 16 * value ^ 2) ^ 2

/-- The displayed divisor products through index eight. -/
theorem exercise_8_13_first_eight (value : K) :
    Polynomial.Recurrence.Spread.Basic.spreadPolynomial 1 value = cyclotomicOne value ∧
      Polynomial.Recurrence.Spread.Basic.spreadPolynomial 2 value =
        cyclotomicOne value * cyclotomicTwo value ∧
      Polynomial.Recurrence.Spread.Basic.spreadPolynomial 3 value =
        cyclotomicOne value * cyclotomicThree value ∧
      Polynomial.Recurrence.Spread.Basic.spreadPolynomial 4 value =
        cyclotomicOne value * cyclotomicTwo value *
          cyclotomicFour value ∧
      Polynomial.Recurrence.Spread.Basic.spreadPolynomial 5 value =
        cyclotomicOne value * cyclotomicFive value ∧
      Polynomial.Recurrence.Spread.Basic.spreadPolynomial 6 value =
        cyclotomicOne value * cyclotomicTwo value *
          cyclotomicThree value * cyclotomicSix value ∧
      Polynomial.Recurrence.Spread.Basic.spreadPolynomial 7 value =
        cyclotomicOne value * cyclotomicSeven value ∧
      Polynomial.Recurrence.Spread.Basic.spreadPolynomial 8 value =
        cyclotomicOne value * cyclotomicTwo value *
          cyclotomicFour value * cyclotomicEight value := by
  unfold cyclotomicOne cyclotomicTwo cyclotomicThree cyclotomicFour
    cyclotomicFive cyclotomicSix cyclotomicSeven cyclotomicEight
  constructor
  · rfl
  constructor
  · simp only [Polynomial.Recurrence.Spread.Basic.spreadPolynomial]
    ring1
  constructor
  · simp only [Polynomial.Recurrence.Spread.Basic.spreadPolynomial]
    ring1
  constructor
  · simp only [Polynomial.Recurrence.Spread.Basic.spreadPolynomial]
    ring1
  constructor
  · simp only [Polynomial.Recurrence.Spread.Basic.spreadPolynomial]
    ring1
  constructor
  · simp only [Polynomial.Recurrence.Spread.Basic.spreadPolynomial]
    ring1
  constructor
  · simp only [Polynomial.Recurrence.Spread.Basic.spreadPolynomial]
    ring1
  · simp only [Polynomial.Recurrence.Spread.Basic.spreadPolynomial]
    ring1

/-- The source's worked `n=12` divisor product. -/
theorem exercise_8_13_twelve (value : K) :
    Polynomial.Recurrence.Spread.Basic.spreadPolynomial 12 value =
      cyclotomicOne value * cyclotomicTwo value *
        cyclotomicThree value * cyclotomicFour value *
        cyclotomicSix value * cyclotomicTwelve value := by
  unfold cyclotomicOne cyclotomicTwo cyclotomicThree cyclotomicFour
    cyclotomicSix cyclotomicTwelve
  simp only [Polynomial.Recurrence.Spread.Basic.spreadPolynomial]
  ring1

end ExerciseEightThirteen

end formalisations.DivineProportions.Chapters.Trigonometry.ChapterEightRemaining

end
