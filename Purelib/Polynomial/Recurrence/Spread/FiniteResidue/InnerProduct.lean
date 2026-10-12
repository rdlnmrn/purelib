module
import Purelib.NumberTheory.Prime.Basic
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.NumberTheory.Prime.ChebyshevSum
import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
import Purelib.Polynomial.Recurrence.Chebyshev.First.FiniteResidue.Sum
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Chebyshev

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Algebra.Field.Cancellation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Prime.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field
open Purelib

open Purelib.Algebra

open Purelib.NumberTheory

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

namespace Purelib.Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct

variable {K : Type*} [ExplicitField K]

section

/-- The exact bounded sum occurring in Exercise 8.11.  Natural residues are
cast one at a time; no carrier, root set, or completed family is enumerated. -/
def spreadInnerProduct
    (primeCardinality firstIndex secondIndex : Nat) : K :=
  FiniteSum.Prefix.prefixSum primeCardinality (fun residue =>
    Recurrence.Spread.Basic.spreadPolynomial firstIndex (residue : K) *
      Recurrence.Spread.Basic.spreadPolynomial secondIndex (residue : K))

/-- The two exceptional values asked for in Exercise 8.11, in the source's
characteristic-free quotient notation. -/
def lowerExceptionalValue : K := -(1 / 16)

/-- The exceptional field value `1 / 16` at the upper index sum. -/
def upperExceptionalValue : K := 1 / 16

/-- The division-free characterizations of the exceptional values. -/
theorem exceptional_values_cleared
  (sixteenNonzero : (16 : K) ≠ 0) :
    lowerExceptionalValue (K := K) * 16 = -1 ∧
      upperExceptionalValue (K := K) * 16 = 1 := by
  constructor
  · unfold lowerExceptionalValue
    simp only [ExplicitField.div_eq_mul_inv]
    rw [show -(1 * (16 : K)⁻¹) * 16 =
      -((16 : K) * (16 : K)⁻¹) by ring1]
    rw [ExplicitField.mul_inv_cancel 16 sixteenNonzero]
  · unfold upperExceptionalValue
    exact ExplicitField.div_mul_cancel 1 sixteenNonzero

end

end Purelib.Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct

end

section
@[expose] public section

/-!
# Divine Proportions, Exercise 8.11

This module proves the book's finite prime-residue inner-product calculation.
Every sum runs over the displayed natural labels `0, ..., p-1`; no ambient
field carrier, primitive root, completed polynomial space, or infinite
orthogonality argument is used.
-/

namespace Purelib.Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct

variable {K : Type*} [ExplicitField K]

section

/-- The bounded spread inner product is symmetric in its two indices. -/
theorem spreadInnerProduct_comm
    (prime first second : Nat) :
    spreadInnerProduct (K := K) prime first second =
      spreadInnerProduct prime second first := by
  unfold spreadInnerProduct
  apply FiniteSum.Prefix.prefixSum_congr
  intro residue residueBelow
  ring1

/-- After clearing the two centered-spread factors and the Chebyshev
product-to-sum factor, the inner product is exactly the Chebyshev sum at the
sum of the indices. -/
theorem
  spreadInnerProduct_chebyshev_cleared_of_le
    (prime first second : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstAtMostSecond : first ≤ second)
    (firstBelow : first < prime - 1) (secondBelow : second < prime - 1) :
    8 * spreadInnerProduct (K := K) prime first second =
      Prime.ChebyshevSum.centeredChebyshevSum prime (first + second) := open Purelib in by
  let center : Nat → K := fun residue => 1 - 2 * (residue : K)
  let productSum := FiniteSum.Prefix.prefixSum prime (fun residue =>
    Recurrence.Chebyshev.First.Basic.chebyshevFirst first (center residue) *
      Recurrence.Chebyshev.First.Basic.chebyshevFirst second (center residue))
  have oneNonzero := Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero
  have pointwise (residue : Nat) :
      4 * (Recurrence.Spread.Basic.spreadPolynomial first (residue : K) *
          Recurrence.Spread.Basic.spreadPolynomial second (residue : K)) =
        1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst first (center residue) -
            Recurrence.Chebyshev.First.Basic.chebyshevFirst second (center residue) +
          Recurrence.Chebyshev.First.Basic.chebyshevFirst first (center residue) *
            Recurrence.Chebyshev.First.Basic.chebyshevFirst second (center residue) := by
    have firstCentered := Recurrence.Spread.Chebyshev.exercise_8_4_cleared first (residue : K)
    have secondCentered := Recurrence.Spread.Chebyshev.exercise_8_4_cleared second (residue : K)
    change 2 * Recurrence.Spread.Basic.spreadPolynomial first (residue : K) =
      1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst first (center residue) at firstCentered
    change 2 * Recurrence.Spread.Basic.spreadPolynomial second (residue : K) =
      1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst second (center residue) at secondCentered
    rw [show 4 * (Recurrence.Spread.Basic.spreadPolynomial first (residue : K) *
          Recurrence.Spread.Basic.spreadPolynomial second (residue : K)) =
        (2 * Recurrence.Spread.Basic.spreadPolynomial first (residue : K)) *
          (2 * Recurrence.Spread.Basic.spreadPolynomial second (residue : K)) by ring1,
      firstCentered, secondCentered]
    ring1
  have fourTimesInner :
      4 * spreadInnerProduct (K := K) prime first second =
        productSum := by
    unfold spreadInnerProduct
    rw [show 4 * FiniteSum.Prefix.prefixSum prime (fun residue =>
          Recurrence.Spread.Basic.spreadPolynomial first (residue : K) *
            Recurrence.Spread.Basic.spreadPolynomial second (residue : K)) =
        FiniteSum.Prefix.prefixSum prime (fun residue =>
          4 * (Recurrence.Spread.Basic.spreadPolynomial first (residue : K) *
            Recurrence.Spread.Basic.spreadPolynomial second (residue : K))) by
          exact (FiniteSum.Prefix.prefixSum_mul_left prime 4 _).symm]
    calc
      FiniteSum.Prefix.prefixSum prime (fun residue =>
          4 * (Recurrence.Spread.Basic.spreadPolynomial first (residue : K) *
            Recurrence.Spread.Basic.spreadPolynomial second (residue : K))) =
        FiniteSum.Prefix.prefixSum prime (fun residue =>
          1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst first (center residue) -
              Recurrence.Chebyshev.First.Basic.chebyshevFirst second (center residue) +
            Recurrence.Chebyshev.First.Basic.chebyshevFirst first (center residue) *
              Recurrence.Chebyshev.First.Basic.chebyshevFirst second (center residue)) := by
                apply FiniteSum.Prefix.prefixSum_congr
                intro residue residueBelow
                exact pointwise residue
      _ = FiniteSum.Prefix.prefixSum prime (fun _ : Nat => (1 : K)) -
            FiniteSum.Prefix.prefixSum prime (fun residue =>
              Recurrence.Chebyshev.First.Basic.chebyshevFirst first (center residue)) -
            FiniteSum.Prefix.prefixSum prime (fun residue =>
              Recurrence.Chebyshev.First.Basic.chebyshevFirst second (center residue)) +
          productSum := by
            unfold productSum
            rw [FiniteSum.Prefix.prefixSum_add,
              FiniteSum.Prefix.prefixSum_sub, FiniteSum.Prefix.prefixSum_sub]
      _ = (prime : K) -
            Prime.ChebyshevSum.centeredChebyshevSum prime first -
            Prime.ChebyshevSum.centeredChebyshevSum prime second + productSum := by
              rw [FiniteSum.Prefix.prefixSum_one,
                ← Prime.ChebyshevSum.centeredChebyshevSum_eq_prefix,
                ← Prime.ChebyshevSum.centeredChebyshevSum_eq_prefix]
      _ = productSum := by
        rw [primeCastZero,
          Prime.ChebyshevSum.prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
            oneNonzero first firstBelow,
          Prime.ChebyshevSum.prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
            oneNonzero second secondBelow]
        ring1
  have productToSum := Prime.ChebyshevSum.centeredChebyshev_product_sum
    (K := K) prime first second firstAtMostSecond
  change 2 * productSum = _ at productToSum
  have differenceBelow : second - first < prime - 1 := by omega0
  have differenceZero := Prime.ChebyshevSum.prime_centered_chebyshev_sum_zero
    (K := K) prime primeIsPrime primeCastZero oneNonzero
      (second - first) differenceBelow
  calc
    8 * spreadInnerProduct (K := K) prime first second =
        2 * (4 * spreadInnerProduct prime first second) := by ring1
    _ = 2 * productSum := by rw [fourTimesInner]
    _ = Prime.ChebyshevSum.centeredChebyshevSum prime (first + second) +
        Prime.ChebyshevSum.centeredChebyshevSum prime (second - first) := productToSum
    _ = Prime.ChebyshevSum.centeredChebyshevSum prime (first + second) := by
      rw [differenceZero, add_zero]

/-- Symmetric version of the cleared inner-product identity. -/
theorem spreadInnerProduct_chebyshev_cleared
    (prime first second : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstBelow : first < prime - 1) (secondBelow : second < prime - 1) :
    8 * spreadInnerProduct (K := K) prime first second =
      Prime.ChebyshevSum.centeredChebyshevSum prime (first + second) := by
  by_cases firstAtMostSecond : first ≤ second
  · exact spreadInnerProduct_chebyshev_cleared_of_le
      prime first second primeIsPrime primeCastZero twoNonzero
        firstAtMostSecond firstBelow secondBelow
  · have secondAtMostFirst : second ≤ first := by omega0
    have reversed := spreadInnerProduct_chebyshev_cleared_of_le
      (K := K) prime second first primeIsPrime primeCastZero twoNonzero
        secondAtMostFirst secondBelow firstBelow
    rw [← spreadInnerProduct_comm prime first second,
      Nat.add_comm] at reversed
    exact reversed

/-- The ordinary case of Exercise 8.11: throughout the requested finite
index box, the bounded inner product vanishes away from the two exceptional
index sums. -/
theorem spreadInnerProduct_zero
    (prime first second : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstPositive : 1 ≤ first) (secondPositive : 1 ≤ second)
    (firstAtMost : first ≤ prime - 2)
    (secondAtMost : second ≤ prime - 2)
    (notLowerExceptional : first + second ≠ prime - 1)
    (notUpperExceptional : first + second ≠ prime + 1) :
    spreadInnerProduct (K := K) prime first second = 0 := open Purelib in
      by
  have firstBelow : first < prime - 1 := by omega0
  have secondBelow : second < prime - 1 := by omega0
  have cleared := spreadInnerProduct_chebyshev_cleared
    (K := K) prime first second primeIsPrime primeCastZero twoNonzero
      firstBelow secondBelow
  have chebyshevZero := Recurrence.Chebyshev.First.FiniteResidue.Sum.prime_centered_chebyshev_sum_regular_zero
    (K := K) prime (first + second) primeIsPrime primeCastZero twoNonzero
      (by omega0) notLowerExceptional notUpperExceptional
  apply ExplicitField.eq_zero_of_mul_eq_zero_left
    ((fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
      (Purelib.Algebra.Field.Characteristic.Nonzero.eight_ne_zero (K := K) twoNonzero : (8 : K) ≠ 0)) twoNonzero)
  rw [cleared, chebyshevZero]

/-- At `m+n=p-1`, the exact exceptional value is `-1/16`. -/
theorem spreadInnerProduct_lower_exceptional
    (prime first second : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstPositive : 1 ≤ first) (secondPositive : 1 ≤ second)
    (_firstAtMost : first ≤ prime - 2)
    (_secondAtMost : second ≤ prime - 2)
    (sumEquation : first + second = prime - 1) :
    spreadInnerProduct (K := K) prime first second =
      lowerExceptionalValue := open Purelib in by
  have oneNonzero := Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero
  have firstBelow : first < prime - 1 := by omega0
  have secondBelow : second < prime - 1 := by omega0
  have innerCleared := spreadInnerProduct_chebyshev_cleared
    (K := K) prime first second primeIsPrime primeCastZero twoNonzero
      firstBelow secondBelow
  rw [sumEquation] at innerCleared
  have boundary := Prime.ChebyshevSum.prime_centered_chebyshev_sum_boundary_cleared
    (K := K) prime primeIsPrime primeCastZero oneNonzero twoNonzero
  have sixteenTimesInner :
      16 * spreadInnerProduct (K := K) prime first second = -1 := by
    calc
      16 * spreadInnerProduct (K := K) prime first second =
          2 * (8 * spreadInnerProduct prime first second) := by ring1
      _ = 2 * Prime.ChebyshevSum.centeredChebyshevSum prime (prime - 1) := by
        rw [innerCleared]
      _ = -1 := boundary
  have exceptional :=
    (exceptional_values_cleared (K := K)
      (Algebra.Field.Characteristic.Nonzero.sixteen_ne_zero twoNonzero)).1
  apply ExplicitField.eq_of_mul_eq_mul_left (Algebra.Field.Characteristic.Nonzero.sixteen_ne_zero
    twoNonzero)
  calc
    16 * spreadInnerProduct (K := K) prime first second = -1 :=
      sixteenTimesInner
    _ = 16 * lowerExceptionalValue (K := K) := by
      rw [show 16 * lowerExceptionalValue (K := K) =
          lowerExceptionalValue * 16 by ring1, exceptional]

/-- At `m+n=p+1`, the exact exceptional value is `1/16`. -/
theorem spreadInnerProduct_upper_exceptional
    (prime first second : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (firstPositive : 1 ≤ first) (secondPositive : 1 ≤ second)
    (firstAtMost : first ≤ prime - 2)
    (secondAtMost : second ≤ prime - 2)
    (sumEquation : first + second = prime + 1) :
    spreadInnerProduct (K := K) prime first second =
      upperExceptionalValue := open Purelib in by
  have firstBelow : first < prime - 1 := by omega0
  have secondBelow : second < prime - 1 := by omega0
  have fourBelowPrime : 4 < prime := by omega0
  have innerCleared := spreadInnerProduct_chebyshev_cleared
    (K := K) prime first second primeIsPrime primeCastZero twoNonzero
      firstBelow secondBelow
  rw [sumEquation] at innerCleared
  have boundary := Recurrence.Chebyshev.First.FiniteResidue.Sum.prime_centered_chebyshev_sum_upper_boundary_cleared
    (K := K) prime primeIsPrime primeCastZero twoNonzero fourBelowPrime
  have sixteenTimesInner :
      16 * spreadInnerProduct (K := K) prime first second = 1 := by
    calc
      16 * spreadInnerProduct (K := K) prime first second =
          2 * (8 * spreadInnerProduct prime first second) := by ring1
      _ = 2 * Prime.ChebyshevSum.centeredChebyshevSum prime (prime + 1) := by
        rw [innerCleared]
      _ = 1 := boundary
  have exceptional :=
    (exceptional_values_cleared (K := K)
      (Algebra.Field.Characteristic.Nonzero.sixteen_ne_zero twoNonzero)).2
  apply ExplicitField.eq_of_mul_eq_mul_left (Algebra.Field.Characteristic.Nonzero.sixteen_ne_zero
    twoNonzero)
  calc
    16 * spreadInnerProduct (K := K) prime first second = 1 :=
      sixteenTimesInner
    _ = 16 * upperExceptionalValue (K := K) := by
      rw [show 16 * upperExceptionalValue (K := K) =
          upperExceptionalValue * 16 by ring1, exceptional]
end

end Purelib.Polynomial.Recurrence.Spread.FiniteResidue.InnerProduct

end
