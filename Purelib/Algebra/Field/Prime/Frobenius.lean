module
import Purelib.Data.Nat.Parity
import Purelib.Algebra.Binomial.Parity
public import Purelib.NumberTheory.Prime.Basic
public import Purelib.Algebra.Field.ExplicitField
import Purelib.NumberTheory.Prime.Binomial

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Ring.Parity
import Purelib.Tactic.Ring

open Purelib.Algebra.Field
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

namespace Purelib.Algebra.Field.Prime.Frobenius

variable {K : Type*} [ExplicitField K]

section ExerciseEightTwo

/-- A prime power fixes the difference between a fixed scalar square and one.

The field has the supplied prime characteristic with nonzero one, the prime is odd, and the center is fixed by that
prime power. -/
theorem square_sub_one_prime_pow
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (primeOdd : Data.Nat.Parity.Odd prime) (center : K)
    (centerPower : center ^ prime = center) :
    (center ^ 2 - 1) ^ prime = center ^ 2 - 1 := open Purelib.NumberTheory.Prime in by
  have squarePower : (center ^ 2) ^ prime = center ^ 2 := by
    calc
      (center ^ 2) ^ prime = center ^ (2 * prime) :=
        (pow_mul center 2 prime).symm
      _ = center ^ (prime * 2) := by
        exact congrArg (fun exponent => center ^ exponent) (Nat.mul_comm 2 prime)
      _ = (center ^ prime) ^ 2 := pow_mul center prime 2
      _ = center ^ 2 := by rw [centerPower]
  have negativeOnePower : (-1 : K) ^ prime = -1 := by
    rcases primeOdd with ⟨half, oddEquation⟩
    have primeEquation : prime = half + half + 1 :=
      oddEquation.trans (congrArg (fun index => index + 1) (Nat.two_mul half))
    rw [primeEquation, Algebra.Binomial.Parity.neg_pow_odd,
      one_pow]
  calc
    (center ^ 2 - 1) ^ prime = (center ^ 2 + (-1)) ^ prime := by
      congr 1
      ring1
    _ = (center ^ 2) ^ prime + (-1 : K) ^ prime :=
      Binomial.prime_add_pow prime primeIsPrime primeCastZero oneNonzero
        (center ^ 2) (-1)
    _ = center ^ 2 - 1 := by rw [squarePower, negativeOnePower]; ring1
end ExerciseEightTwo

end Purelib.Algebra.Field.Prime.Frobenius

end
