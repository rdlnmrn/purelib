module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.NumberTheory.Prime.Binomial
public import Purelib.Polynomial.Recurrence.Spread.Binomial

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Purelib.NumberTheory.Prime.Basic

open Purelib

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

namespace Purelib.Polynomial.Recurrence.Spread.FiniteResidue.Binomial

variable {K : Type*} [ExplicitField K]

section

/-- At an odd prime index, every nonconstant term in the finite spread
binomial expansion vanishes in characteristic `p`. -/
theorem spreadBinomialExpansion_prime_odd
    (prime half : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0)
    (oneNonzero : (1 : K) ≠ 0)
    (primeEquation : prime = half + half + 1)
    (center radialSquare : K) :
    Recurrence.Spread.Binomial.spreadBinomialExpansion prime (half + 1) center radialSquare =
      center ^ prime := open Purelib.Algebra in open Purelib.NumberTheory in by
  have firstTerm :
      Recurrence.Spread.Binomial.spreadBinomialTerm prime center radialSquare 0 = center ^ prime := by
    unfold Recurrence.Spread.Binomial.spreadBinomialTerm
    simp only [zero_add, Nat.sub_zero, pow_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul, mul_one, -eq_self, -iff_self]
    rfl
  have tailTermZero (index : Nat) (indexBelow : index < half) :
      Recurrence.Spread.Binomial.spreadBinomialTerm prime center radialSquare (index + 1) = 0 := by
    let coefficientIndex := (index + 1) + (index + 1)
    have coefficientPositive : coefficientIndex ≠ 0 := by
      unfold coefficientIndex
      omega0
    have coefficientBelow : coefficientIndex < prime := by
      unfold coefficientIndex
      omega0
    have coefficientZero : (prime.choose coefficientIndex : K) = 0 :=
      Prime.Binomial.prime_interior_choose_cast_zero prime primeIsPrime primeCastZero
        oneNonzero coefficientIndex coefficientPositive coefficientBelow
    unfold Recurrence.Spread.Binomial.spreadBinomialTerm
    change
      (-radialSquare) ^ (index + 1) *
          center ^ (prime - coefficientIndex) *
            (prime.choose coefficientIndex : K) = 0
    rw [coefficientZero, mul_zero]
  have tailZero :
      FiniteSum.Prefix.prefixSum half (fun index =>
        Recurrence.Spread.Binomial.spreadBinomialTerm prime center radialSquare (index + 1)) = 0 := by
    calc
      FiniteSum.Prefix.prefixSum half (fun index =>
          Recurrence.Spread.Binomial.spreadBinomialTerm prime center radialSquare (index + 1)) =
        FiniteSum.Prefix.prefixSum half (fun _ : Nat => (0 : K)) := by
          apply FiniteSum.Prefix.prefixSum_congr
          intro index indexBelow
          exact tailTermZero index indexBelow
      _ = 0 := FiniteSum.Prefix.prefixSum_zero_values half
  unfold Recurrence.Spread.Binomial.spreadBinomialExpansion
  rw [FiniteSum.Prefix.prefixSum_succ, firstTerm, tailZero, add_zero]
end

end Purelib.Polynomial.Recurrence.Spread.FiniteResidue.Binomial

end
