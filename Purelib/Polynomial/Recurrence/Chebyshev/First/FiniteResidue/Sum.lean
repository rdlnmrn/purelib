module
import Purelib.NumberTheory.Prime.Basic
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.FiniteSum.Prefix
public import Purelib.NumberTheory.Prime.ChebyshevSum
import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
import Purelib.Polynomial.Recurrence.Chebyshev.First.FiniteResidue.Frobenius

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Prime.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field
open Purelib

open Purelib.NumberTheory

section
@[expose] public section

/-!
# Divine Proportions, Exercise 8.11

This module proves the book's finite prime-residue inner-product calculation.
Every sum runs over the displayed natural labels `0, ..., p-1`; no ambient
field carrier, primitive root, completed polynomial space, or infinite
orthogonality argument is used.
-/

namespace Purelib.Polynomial.Recurrence.Chebyshev.First.FiniteResidue.Sum

variable {K : Type*} [ExplicitField K]

section ExerciseEightEleven

/-- Consequently the bounded sum at index `p` is the already-vanishing sum
at index one. -/
theorem prime_centered_chebyshev_sum_prime_zero
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0) :
    Prime.ChebyshevSum.centeredChebyshevSum (K := K) prime prime = 0 := open Purelib in open Purelib.Algebra in open
      Purelib.Polynomial in by
  have oneNonzero := Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero
  have primeNotTwo : prime ≠ 2 := by
    intro primeEqualsTwo
    apply twoNonzero
    simpa only [primeEqualsTwo, Nat.cast_ofNat] using primeCastZero
  have oneBelow : 1 < prime - 1 := by
    have twoAtMost := NumberTheory.Prime.two_le primeIsPrime
    omega0
  rw [Prime.ChebyshevSum.centeredChebyshevSum_eq_prefix]
  calc
    FiniteSum.Prefix.prefixSum prime (fun residue =>
        Recurrence.Chebyshev.First.Basic.chebyshevFirst prime (1 - 2 * (residue : K))) =
      FiniteSum.Prefix.prefixSum prime (fun residue =>
        Recurrence.Chebyshev.First.Basic.chebyshevFirst 1 (1 - 2 * (residue : K))) := by
          apply FiniteSum.Prefix.prefixSum_congr
          intro residue residueBelow
          rw [Recurrence.Chebyshev.First.FiniteResidue.Frobenius.chebyshevFirst_prime_centered_residue prime residue
            primeIsPrime primeCastZero twoNonzero,
            Recurrence.Chebyshev.First.Basic.chebyshevFirst_one]
    _ = Prime.ChebyshevSum.centeredChebyshevSum (K := K) prime 1 :=
      (Prime.ChebyshevSum.centeredChebyshevSum_eq_prefix prime 1).symm
    _ = 0 := Prime.ChebyshevSum.prime_centered_chebyshev_sum_zero prime primeIsPrime
      primeCastZero oneNonzero 1 oneBelow

/-- Frobenius at the centered labels reflects Chebyshev sums across index
`p`: `A_(p+t)+A_(p-t)=A_(t+1)+A_(t-1)`. -/
theorem prime_centered_chebyshev_sum_reflection
    (prime step : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (stepPositive : 1 ≤ step) (stepAtMostPrime : step ≤ prime) :
    Prime.ChebyshevSum.centeredChebyshevSum (K := K) prime (prime + step) +
        Prime.ChebyshevSum.centeredChebyshevSum prime (prime - step) =
      Prime.ChebyshevSum.centeredChebyshevSum prime (step + 1) +
        Prime.ChebyshevSum.centeredChebyshevSum prime (step - 1) := open Purelib.Algebra in open Purelib.Polynomial in
          by
  let center : Nat → K := fun residue => 1 - 2 * (residue : K)
  let upperProduct := FiniteSum.Prefix.prefixSum prime (fun residue =>
    Recurrence.Chebyshev.First.Basic.chebyshevFirst step (center residue) *
      Recurrence.Chebyshev.First.Basic.chebyshevFirst prime (center residue))
  let lowerProduct := FiniteSum.Prefix.prefixSum prime (fun residue =>
    Recurrence.Chebyshev.First.Basic.chebyshevFirst 1 (center residue) *
      Recurrence.Chebyshev.First.Basic.chebyshevFirst step (center residue))
  have productsEqual : upperProduct = lowerProduct := by
    unfold upperProduct lowerProduct
    apply FiniteSum.Prefix.prefixSum_congr
    intro residue residueBelow
    rw [Recurrence.Chebyshev.First.FiniteResidue.Frobenius.chebyshevFirst_prime_centered_residue prime residue
      primeIsPrime
      primeCastZero twoNonzero, Recurrence.Chebyshev.First.Basic.chebyshevFirst_one]
    ring1
  have upper := Prime.ChebyshevSum.centeredChebyshev_product_sum
    (K := K) prime step prime stepAtMostPrime
  have lower := Prime.ChebyshevSum.centeredChebyshev_product_sum
    (K := K) prime 1 step stepPositive
  change 2 * upperProduct = _ at upper
  change 2 * lowerProduct = _ at lower
  calc
    Prime.ChebyshevSum.centeredChebyshevSum (K := K) prime (prime + step) +
        Prime.ChebyshevSum.centeredChebyshevSum prime (prime - step) =
      2 * upperProduct := by
        rw [upper]
        rw [Nat.add_comm]
    _ = 2 * lowerProduct := by rw [productsEqual]
    _ = Prime.ChebyshevSum.centeredChebyshevSum prime (1 + step) +
        Prime.ChebyshevSum.centeredChebyshevSum prime (step - 1) := lower
    _ = Prime.ChebyshevSum.centeredChebyshevSum prime (step + 1) +
        Prime.ChebyshevSum.centeredChebyshevSum prime (step - 1) := by
          rw [Nat.add_comm]

open Purelib.Polynomial
/-- All reflected sums strictly beyond the upper exceptional index and still
within the Exercise 8.11 range vanish. -/
theorem prime_centered_chebyshev_sum_high_zero
    (prime step : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (twoAtMostStep : 2 ≤ step) (stepAtMost : step ≤ prime - 4) :
    Prime.ChebyshevSum.centeredChebyshevSum (K := K) prime (prime + step) = 0 := open Purelib in by
  have oneNonzero := Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero
  have reflection := Recurrence.Chebyshev.First.FiniteResidue.Sum.prime_centered_chebyshev_sum_reflection
    (K := K) prime step primeIsPrime primeCastZero twoNonzero
      (by omega0) (by omega0)
  rw [Prime.ChebyshevSum.prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
      oneNonzero (prime - step) (by omega0),
    Prime.ChebyshevSum.prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
      oneNonzero (step + 1) (by omega0),
    Prime.ChebyshevSum.prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
      oneNonzero (step - 1) (by omega0),
    add_zero, zero_add] at reflection
  exact reflection

/-- The upper exceptional Chebyshev sum has the opposite cleared value from
the Fermat-boundary sum. -/
theorem
  prime_centered_chebyshev_sum_upper_boundary_cleared
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (fourBelowPrime : 4 < prime) :
    2 * Prime.ChebyshevSum.centeredChebyshevSum (K := K) prime (prime + 1) = 1 := open Purelib in by
  have oneNonzero := Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero
  have reflection := Recurrence.Chebyshev.First.FiniteResidue.Sum.prime_centered_chebyshev_sum_reflection
    (K := K) prime 1 primeIsPrime primeCastZero twoNonzero
      (by omega0) (by omega0)
  rw [show prime - 1 = prime - 1 by rfl,
    Prime.ChebyshevSum.prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
      oneNonzero 2 (by omega0),
    Prime.ChebyshevSum.prime_centered_chebyshev_sum_zero prime primeIsPrime primeCastZero
      oneNonzero 0 (by omega0),
    add_zero] at reflection
  have lowerBoundary := Prime.ChebyshevSum.prime_centered_chebyshev_sum_boundary_cleared
    (K := K) prime primeIsPrime primeCastZero oneNonzero twoNonzero
  calc
    2 * Prime.ChebyshevSum.centeredChebyshevSum (K := K) prime (prime + 1) =
        -(2 * Prime.ChebyshevSum.centeredChebyshevSum prime (prime - 1)) := by
          rw [show Prime.ChebyshevSum.centeredChebyshevSum (K := K) prime (prime + 1) =
              -Prime.ChebyshevSum.centeredChebyshevSum prime (prime - 1) by
                exact eq_neg_of_add_eq_zero_left reflection]
          ring1
    _ = 1 := by rw [lowerBoundary]; ring1

/-- Complete zero classification for the sum indices that can occur in
Exercise 8.11, excluding its two displayed exceptional indices. -/
theorem prime_centered_chebyshev_sum_regular_zero
    (prime index : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : K) = 0) (twoNonzero : (2 : K) ≠ 0)
    (indexAtMost : index ≤ prime + prime - 4)
    (notLowerBoundary : index ≠ prime - 1)
    (notUpperBoundary : index ≠ prime + 1) :
    Prime.ChebyshevSum.centeredChebyshevSum (K := K) prime index = 0 := open Purelib in by
  have oneNonzero := Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero twoNonzero
  by_cases belowBoundary : index < prime - 1
  · exact Prime.ChebyshevSum.prime_centered_chebyshev_sum_zero prime primeIsPrime
      primeCastZero oneNonzero index belowBoundary
  · by_cases indexAtMostPrime : index ≤ prime
    · have indexEqualsPrime : index = prime := by omega0
      subst index
      exact Recurrence.Chebyshev.First.FiniteResidue.Sum.prime_centered_chebyshev_sum_prime_zero prime primeIsPrime
        primeCastZero twoNonzero
    · let step := index - prime
      have indexEquation : index = prime + step := by
        unfold step
        omega0
      have twoAtMostStep : 2 ≤ step := by
        unfold step
        omega0
      have stepAtMost : step ≤ prime - 4 := by
        unfold step
        omega0
      rw [indexEquation]
      exact Recurrence.Chebyshev.First.FiniteResidue.Sum.prime_centered_chebyshev_sum_high_zero prime step primeIsPrime
        primeCastZero twoNonzero twoAtMostStep stepAtMost
end ExerciseEightEleven

end Purelib.Polynomial.Recurrence.Chebyshev.First.FiniteResidue.Sum

end
