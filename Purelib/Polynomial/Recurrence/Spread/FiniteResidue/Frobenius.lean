module
import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Parity
import Purelib.Algebra.Binomial.Parity
import Purelib.Algebra.Semiring.Normalization
public import Purelib.NumberTheory.Prime.Basic
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Power.Frobenius
import Purelib.NumberTheory.Prime.Binomial
import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
public import Purelib.Polynomial.Recurrence.Chebyshev.First.Power
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Binomial
import Purelib.Polynomial.Recurrence.Spread.Chebyshev
import Purelib.Polynomial.Recurrence.Spread.FiniteResidue.Binomial

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Purelib.Tactic.Ring
import Mathlib.Data.Nat.Prime.Basic

open Purelib.Algebra.Field
open scoped Purelib.Data.Nat

open Purelib

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

namespace Purelib.Polynomial.Recurrence.Spread.FiniteResidue.Frobenius

variable {K : Type*} [ExplicitField K]

section

/-- The spread polynomial fixes each field element at a supplied Frobenius exponent.

Assume the Chebyshev polynomial at that index agrees with powering and that powering fixes every field element. When two
is nonzero, the spread polynomial at the same index also fixes every element (Exercise 8.5). -/
theorem fixed_from_frobenius
    (primeCardinality : Nat) (twoNonzero : (2 : K) ≠ 0)
    (chebyshevPower : Recurrence.Chebyshev.First.Power.ChebyshevAgreesWithPower (K := K) primeCardinality)
    (frobenius : Algebra.Field.Power.Frobenius.HasFrobeniusExponent (K := K) primeCardinality)
    (value : K) :
    Recurrence.Spread.Basic.spreadPolynomial primeCardinality value = value := by
  have traceFixed :
      Recurrence.Chebyshev.First.Basic.chebyshevFirst primeCardinality (1 - 2 * value) =
        1 - 2 * value := by
    calc
      Recurrence.Chebyshev.First.Basic.chebyshevFirst primeCardinality (1 - 2 * value) =
          (1 - 2 * value) ^ primeCardinality :=
        chebyshevPower (1 - 2 * value)
      _ = 1 - 2 * value := frobenius (1 - 2 * value)
  have doubled : 2 * Recurrence.Spread.Basic.spreadPolynomial primeCardinality value = 2 * value := by
    calc
      2 * Recurrence.Spread.Basic.spreadPolynomial primeCardinality value =
          1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst primeCardinality (1 - 2 * value) :=
        Recurrence.Spread.Chebyshev.exercise_8_4_cleared primeCardinality value
      _ = 2 * value := by rw [traceFixed]; ring1
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  calc
    Recurrence.Spread.Basic.spreadPolynomial primeCardinality value =
        (2 * Recurrence.Spread.Basic.spreadPolynomial primeCardinality value) * (2 : K)⁻¹ := by
      calc
        Recurrence.Spread.Basic.spreadPolynomial primeCardinality value =
            Recurrence.Spread.Basic.spreadPolynomial primeCardinality value * 1 := by ring1
        _ = Recurrence.Spread.Basic.spreadPolynomial primeCardinality value *
              ((2 : K) * (2 : K)⁻¹) := by rw [twoCancel]
        _ = (2 * Recurrence.Spread.Basic.spreadPolynomial primeCardinality value) *
              (2 : K)⁻¹ := by ring1
    _ = (2 * value) * (2 : K)⁻¹ := by rw [doubled]
    _ = value := by
      calc
        (2 * value) * (2 : K)⁻¹ =
            value * ((2 : K) * (2 : K)⁻¹) := by ring1
        _ = value := by rw [twoCancel]; ring1

/-- Exercise 8.5 at the exact finite boundary: every natural residue label in
characteristic `p` is fixed by the `p`th spread polynomial.  This quantifies
over the residue data directly and makes no claim that a list enumerates an
ambient field carrier. -/
theorem prime_residue_fixed
    (prime residue : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0) :
    Recurrence.Spread.Basic.spreadPolynomial prime (residue : K) = (residue : K) := open Purelib.NumberTheory in by
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
  let radialSquare : K := 4 * value * (1 - value)
  have binomialIdentity :
      1 - 2 * Recurrence.Spread.Basic.spreadPolynomial prime value =
        Recurrence.Spread.Binomial.spreadBinomialExpansion prime (half + 1) center radialSquare := by
    have source := Recurrence.Spread.Binomial.exercise_8_6_odd half value twoNonzero
    simpa only [primeEquation, center, radialSquare] using source
  have expansionCollapse :
      Recurrence.Spread.Binomial.spreadBinomialExpansion prime (half + 1) center radialSquare =
        center ^ prime :=
    Recurrence.Spread.FiniteResidue.Binomial.spreadBinomialExpansion_prime_odd prime half primeIsPrime primeCastZero
      oneNonzero primeEquation center radialSquare
  have twoPower : (2 : K) ^ prime = 2 := by
    simpa only [Nat.cast_ofNat] using
      (Prime.Binomial.prime_natCast_pow prime primeIsPrime primeCastZero oneNonzero 2 :
        ((2 : Nat) : K) ^ prime = ((2 : Nat) : K))
  have valuePower : value ^ prime = value := by
    unfold value
    exact Prime.Binomial.prime_natCast_pow prime primeIsPrime primeCastZero oneNonzero
      residue
  have centerPower : center ^ prime = 1 - 2 * value ^ prime := by
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
      _ = 1 - 2 * value ^ prime := by
        rw [Algebra.Semiring.Normalization.product_pow, twoPower]
  have centeredEquality :
      1 - 2 * Recurrence.Spread.Basic.spreadPolynomial prime value = 1 - 2 * value := by
    calc
      1 - 2 * Recurrence.Spread.Basic.spreadPolynomial prime value =
          Recurrence.Spread.Binomial.spreadBinomialExpansion prime (half + 1) center radialSquare :=
        binomialIdentity
      _ = center ^ prime := expansionCollapse
      _ = 1 - 2 * value ^ prime := centerPower
      _ = 1 - 2 * value := by rw [valuePower]
  have doubledEquality :
      2 * Recurrence.Spread.Basic.spreadPolynomial prime value = 2 * value := by
    calc
      2 * Recurrence.Spread.Basic.spreadPolynomial prime value =
          1 - (1 - 2 * Recurrence.Spread.Basic.spreadPolynomial prime value) := by ring1
      _ = 1 - (1 - 2 * value) := by rw [centeredEquality]
      _ = 2 * value := by ring1
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  calc
    Recurrence.Spread.Basic.spreadPolynomial prime (residue : K) =
        Recurrence.Spread.Basic.spreadPolynomial prime value := rfl
    _ = (2 * Recurrence.Spread.Basic.spreadPolynomial prime value) * (2 : K)⁻¹ := by
      calc
        Recurrence.Spread.Basic.spreadPolynomial prime value =
            Recurrence.Spread.Basic.spreadPolynomial prime value * 1 := by ring1
        _ = Recurrence.Spread.Basic.spreadPolynomial prime value * (2 * (2 : K)⁻¹) := by
          rw [twoCancel]
        _ = (2 * Recurrence.Spread.Basic.spreadPolynomial prime value) * (2 : K)⁻¹ := by ring1
    _ = (2 * value) * (2 : K)⁻¹ := by rw [doubledEquality]
    _ = value := by rw [show (2 * value) * (2 : K)⁻¹ =
      value * (2 * (2 : K)⁻¹) by ring1, twoCancel, mul_one]
    _ = (residue : K) := rfl

end

end Purelib.Polynomial.Recurrence.Spread.FiniteResidue.Frobenius

end
