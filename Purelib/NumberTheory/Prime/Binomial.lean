module
public import Purelib.NumberTheory.Prime.Basic
import Purelib.Algebra.NatCast
import Purelib.Data.Nat.Choose
import Purelib.Data.Nat.Divisibility
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Nat.GCD.Extended
public import Purelib.Algebra.Field.ExplicitField

import Mathlib.Data.Nat.Prime.Basic
import Purelib.Algebra.Binomial
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs

open Purelib.Algebra.Field

open Purelib

section
public section

/-!
# Finite prime-binomial arithmetic

This module isolates the constructive finite arithmetic needed for prime-field
calculations.  A prime binomial expansion has only its two endpoint terms in
characteristic `p`; all interior coefficients vanish through Pascal's finite
multiplicative recurrence.  The needed nonzero natural casts are certified by
the executable extended Euclidean algorithm, without a field-carrier
enumeration or a choice-bearing binomial-divisibility theorem.
-/

namespace Purelib.NumberTheory.Prime.Binomial

open Purelib.Algebra
open Purelib.Data.Nat

variable {R : Type*} [ExplicitField R]

/-- A positive natural strictly below `p` has nonzero cast in a nontrivial
explicit field of characteristic `p`.  The proof uses the executable extended
Euclidean algorithm: primality makes the two naturals coprime, and their
computed Bezout coefficients would otherwise force `1 = 0`. -/
theorem prime_interior_natCast_ne_zero
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (index : Nat) (indexPositive : index ≠ 0) (indexBelow : index < prime) :
    (index : R) ≠ 0 := open Purelib.Algebra in open Purelib in by
  intro indexCastZero
  let result := Data.Nat.GCD.Extended.compute prime index
  have specification := Data.Nat.GCD.Extended.compute_spec prime index
  have gcdEqualsOne : result.gcd = 1 := by
    rcases (NumberTheory.Prime.eq_one_or_self_of_dvd primeIsPrime) result.gcd
        specification.2.1 with equalsOne | equalsPrime
    · exact equalsOne
    · have primeLeIndex : prime ≤ index := by
        rw [← equalsPrime]
        exact Divisibility.le_of_dvd (Nat.pos_of_ne_zero indexPositive)
          specification.2.2
      exact (Nat.not_le_of_lt indexBelow primeLeIndex).elim
  have bezout := specification.1
  have castBezout := congrArg (fun value : Int => (value : R)) bezout
  have computedGcdEqualsOne :
      (Data.Nat.GCD.Extended.compute prime index).gcd = 1 := gcdEqualsOne
  have oneCastInt : ((1 : Nat) : Int) = 1 := rfl
  have oneCastField : ((1 : Nat) : R) = 1 := Nat.cast_one
  apply oneNonzero
  simpa only [-eq_self, -iff_self, computedGcdEqualsOne, oneCastInt, oneCastField, Int.cast_one, Ring.IntCast.add,
    Ring.IntCast.intCast_mul, Int.cast_natCast, primeCastZero,
    indexCastZero, zero_mul, mul_zero, zero_add]
    using castBezout

/-- Every strictly interior binomial coefficient in a prime row casts to zero
when the prime itself casts to zero.  This proof uses Pascal's finite
multiplicative recurrence and explicit field cancellation; it does not use the
choice-bearing upstream divisibility convenience theorem. -/
theorem prime_interior_choose_cast_zero
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (index : Nat) (indexPositive : index ≠ 0) (indexBelow : index < prime) :
    (prime.choose index : R) = 0 := by
  obtain ⟨last, primeEquation⟩ := Nat.exists_eq_succ_of_ne_zero
    (NumberTheory.Prime.ne_zero primeIsPrime)
  obtain ⟨previous, indexEquation⟩ := Nat.exists_eq_succ_of_ne_zero
    indexPositive
  subst prime
  subst index
  have naturalRecurrence := Choose.add_one_mul_choose_eq last previous
  have castRecurrence := congrArg (fun value : Nat => (value : R))
    naturalRecurrence
  simp only [-eq_self, -iff_self, NatCast.mul] at castRecurrence
  have indexCastNonzero : ((previous + 1 : Nat) : R) ≠ 0 :=
    prime_interior_natCast_ne_zero (last + 1) primeIsPrime primeCastZero
      oneNonzero (previous + 1) (by omega0) indexBelow
  have productZero :
      (((last + 1).choose (previous + 1) : Nat) : R) *
          ((previous + 1 : Nat) : R) = 0 := by
    rw [← castRecurrence, primeCastZero, zero_mul]
  have inverseCancel :
      ((previous + 1 : Nat) : R) * ((previous + 1 : Nat) : R)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel _ indexCastNonzero
  calc
    (((last + 1).choose (previous + 1) : Nat) : R) =
        (((last + 1).choose (previous + 1) : Nat) : R) * 1 := by
      rw [mul_one]
    _ = (((last + 1).choose (previous + 1) : Nat) : R) *
          (((previous + 1 : Nat) : R) *
            ((previous + 1 : Nat) : R)⁻¹) := by
      rw [inverseCancel]
    _ = ((((last + 1).choose (previous + 1) : Nat) : R) *
          ((previous + 1 : Nat) : R)) *
            ((previous + 1 : Nat) : R)⁻¹ := by rw [mul_assoc]
    _ = 0 := by rw [productZero, zero_mul]

/-- Freshman's dream proved from the explicitly bounded binomial expansion.
No polynomial object or unbounded sum is introduced. -/
theorem prime_add_pow
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (left right : R) :
    (left + right) ^ prime = left ^ prime + right ^ prime :=
  open Purelib in Algebra.Binomial.add_pow_eq_endpoints_of_interior_choose_cast_zero prime
    (NumberTheory.Prime.ne_zero primeIsPrime)
    (fun index indexPositive indexBelow =>
      prime_interior_choose_cast_zero prime primeIsPrime primeCastZero
        oneNonzero index indexPositive indexBelow)
    left right

/-- Every natural residue label satisfies Frobenius in characteristic `p`.
The induction uses only the finite prime-binomial identity. -/
theorem prime_natCast_pow
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (residue : Nat) :
    (residue : R) ^ prime = (residue : R) := by
  induction residue with
  | zero =>
      simp only [Nat.cast_zero]
      exact zero_pow (NumberTheory.Prime.ne_zero primeIsPrime)
  | succ residue inductionHypothesis =>
      rw [Nat.cast_succ,
        prime_add_pow prime primeIsPrime primeCastZero oneNonzero,
        inductionHypothesis, one_pow]

end Purelib.NumberTheory.Prime.Binomial

end
