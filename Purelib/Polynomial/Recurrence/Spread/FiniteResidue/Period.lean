module
import Purelib.Algebra.Binomial.Parity
import Purelib.Algebra.Semiring.Normalization
import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Parity
public import Purelib.NumberTheory.Prime.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Multiplication
import Purelib.NumberTheory.Prime.Binomial
import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
import Purelib.Polynomial.Recurrence.Chebyshev.First.FiniteResidue.Period
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Chebyshev
import Purelib.Polynomial.Recurrence.Spread.Period

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Purelib.Tactic.Ring
import Mathlib.Data.Nat.Prime.Basic

open Purelib.Algebra.Field
open scoped Purelib.Data.Nat
open Purelib
open Purelib.Data.Nat

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

namespace Purelib.Polynomial.Recurrence.Spread.FiniteResidue.Period

variable {K : Type*} [ExplicitField K]

section

/-- The period proposed in Exercise 8.2, computed by ordinary finite natural
number arithmetic. -/
def gohPeriod (primeCardinality : Nat) : Nat :=
  (primeCardinality - 1) * (primeCardinality + 1) / 2

/-- For an odd number `p=2h+1`, Goh's displayed period is the ordinary
finite product `h(p+1)`.  This is the division-free form used by the power
calculation. -/
theorem gohPeriod_odd
    (prime half : Nat) (primeEquation : prime = half + half + 1) :
    gohPeriod prime = half * (prime + 1) := by
  subst prime
  unfold gohPeriod
  rw [show half + half + 1 - 1 = 2 * half by omega0]
  rw [show (2 * half) * (half + half + 1 + 1) =
      2 * (half * (half + half + 1 + 1)) by rw [Multiplication.mul_assoc]]
  exact Division.mul_div_cancel_left _ (by decide : 0 < 2)

/-- Exercise 8.2 reduces to two explicitly checkable recurrence seeds.  Once
the prime-field calculation supplies these two identities at the proposed
period, the second-order recurrence proves every requested index without an
unbounded sequence. -/
theorem period_from_seeds
    (primeCardinality index : Nat) (value : K)
    (zeroSeed :
      Recurrence.Spread.Basic.spreadPolynomial (gohPeriod primeCardinality) value
        = 0)
    (oneSeed :
      Recurrence.Spread.Basic.spreadPolynomial (gohPeriod primeCardinality + 1)
        value = value) :
    Recurrence.Spread.Basic.spreadPolynomial (index + gohPeriod primeCardinality)
      value =
      Recurrence.Spread.Basic.spreadPolynomial index value :=
  Recurrence.Spread.Period.spreadPolynomial_period (gohPeriod primeCardinality)
    value
    zeroSeed oneSeed index

/-- Exercise 8.2 at the constructive finite-field boundary.  For every
natural residue label in an odd prime characteristic with decidable equality,
the spread-polynomial orbit has Goh's period `(p-1)(p+1)/2`.  The proof never
lists the elements of the field; it uses only the supplied residue, finite
prime-binomial arithmetic, and the executable quadratic pair. -/
theorem prime_residue_period
    [DecidableEq K]
    (prime residue index : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0) :
    Recurrence.Spread.Basic.spreadPolynomial (index + gohPeriod prime) (residue :
      K) =
      Recurrence.Spread.Basic.spreadPolynomial index (residue : K) := open Purelib.NumberTheory in by
  have oneNonzero : (1 : K) ≠ 0 := by
    intro oneEqualsZero
    apply twoNonzero
    have twoAsOnes : (2 : K) = (1 : K) + (1 : K) := by
      change ((1 + 1 : Nat) : K) = (1 : K) + (1 : K)
      rw [Algebra.NatCast.add, Nat.cast_one]
    rw [twoAsOnes, oneEqualsZero, zero_add]
  have primeNotTwo : prime ≠ 2 := by
    intro primeEqualsTwo
    apply twoNonzero
    simpa only [primeEqualsTwo, Nat.cast_ofNat] using primeCastZero
  have primeOdd : Data.Nat.Parity.Odd prime := NumberTheory.Prime.odd_of_ne_two primeIsPrime primeNotTwo
  rcases primeOdd with ⟨half, oddEquation⟩
  have primeEquation : prime = half + half + 1 := by omega0
  let value : K := residue
  let center : K := 1 - 2 * value
  have valuePower : value ^ prime = value := by
    unfold value
    exact Prime.Binomial.prime_natCast_pow prime primeIsPrime primeCastZero oneNonzero
      residue
  have twoPower : (2 : K) ^ prime = 2 := by
    simpa only [Nat.cast_ofNat] using
      (Prime.Binomial.prime_natCast_pow prime primeIsPrime primeCastZero oneNonzero 2 :
        ((2 : Nat) : K) ^ prime = ((2 : Nat) : K))
  have centerPower : center ^ prime = center := by
    have negativePower : (-(2 * value)) ^ prime = -(2 * value) ^ prime := by
      rw [primeEquation, Algebra.Binomial.Parity.neg_pow_odd]
    calc
      center ^ prime = (1 + -(2 * value)) ^ prime := by
        congr 1
        unfold center
        ring1
      _ = 1 ^ prime + (-(2 * value)) ^ prime :=
        Prime.Binomial.prime_add_pow prime primeIsPrime primeCastZero oneNonzero 1
          (-(2 * value))
      _ = 1 - (2 * value) ^ prime := by
        rw [one_pow, negativePower]
        ring1
      _ = 1 - 2 * value ^ prime := by rw [Algebra.Semiring.Normalization.product_pow, twoPower]
      _ = center := by rw [valuePower]
  have chebyshevSeeds := Recurrence.Chebyshev.First.FiniteResidue.Period.prime_chebyshev_period_seeds
    prime half primeIsPrime primeCastZero oneNonzero twoNonzero
    primeEquation center centerPower
  have periodEquation : gohPeriod prime = half * (prime + 1) :=
    gohPeriod_odd prime half primeEquation
  have zeroSeed : Recurrence.Spread.Basic.spreadPolynomial (gohPeriod prime)
    value = 0 := by
    have doubledZero :
        2 * Recurrence.Spread.Basic.spreadPolynomial (gohPeriod prime) value = 0
          := by
      calc
        2 * Recurrence.Spread.Basic.spreadPolynomial (gohPeriod prime) value =
            1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst (gohPeriod prime)
              center := by
          unfold center
          exact Recurrence.Spread.Chebyshev.exercise_8_4_cleared (gohPeriod
            prime) value
        _ = 0 := by rw [periodEquation, chebyshevSeeds.1]; ring1
    exact ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero doubledZero
  have oneSeed : Recurrence.Spread.Basic.spreadPolynomial (gohPeriod prime + 1)
    value = value := by
    have doubledEqual :
        2 * Recurrence.Spread.Basic.spreadPolynomial (gohPeriod prime + 1) value
          = 2 * value := by
      calc
        2 * Recurrence.Spread.Basic.spreadPolynomial (gohPeriod prime + 1) value
          =
            1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst (gohPeriod prime
              + 1) center := by
          unfold center
          exact Recurrence.Spread.Chebyshev.exercise_8_4_cleared (gohPeriod prime
            + 1) value
        _ = 1 - center := by
          rw [periodEquation, chebyshevSeeds.2]
        _ = 2 * value := by unfold center; ring1
    exact ExplicitField.eq_of_mul_eq_mul_left twoNonzero doubledEqual
  change Recurrence.Spread.Basic.spreadPolynomial (index + gohPeriod prime) value
    =
    Recurrence.Spread.Basic.spreadPolynomial index value
  exact period_from_seeds prime index value zeroSeed oneSeed

end

end Purelib.Polynomial.Recurrence.Spread.FiniteResidue.Period

end
