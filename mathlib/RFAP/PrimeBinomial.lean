import mathlib.RFAP.FiniteBinomial
import mathlib.RFAP.ExplicitField
import mathlib.RFAP.CanonicalGCD
import Mathlib.Data.Nat.Prime.Basic
import mathlib.Tactic.QuotientFreeOmega

/-!
# Finite prime-binomial arithmetic

This module isolates the constructive finite arithmetic needed for prime-field
calculations.  A prime binomial expansion has only its two endpoint terms in
characteristic `p`; all interior coefficients vanish through Pascal's finite
multiplicative recurrence.  The needed nonzero natural casts are certified by
the executable extended Euclidean algorithm, without a field-carrier
enumeration or a choice-bearing binomial-divisibility theorem.
-/

namespace RFAP

variable {R : Type*} [ExplicitField R]

/-- A finite binomial expansion collapses to its two endpoint terms whenever
all strictly interior coefficients cast to zero.  This ring-level lemma keeps
the cancellation needed to establish those coefficient equations separate
from their use in a quadratic pair or another finite algebra. -/
theorem add_pow_eq_endpoints_of_interior_choose_cast_zero
    {S : Type*} [CommRing S]
    (exponent : Nat) (exponentNonzero : exponent ≠ 0)
    (interiorZero : ∀ index : Nat, index ≠ 0 → index < exponent →
      (exponent.choose index : S) = 0)
    (left right : S) :
    (left + right) ^ exponent = left ^ exponent + right ^ exponent := by
  obtain ⟨last, exponentEquation⟩ := Nat.exists_eq_succ_of_ne_zero
    exponentNonzero
  subst exponent
  let term : Nat → S := fun index =>
    right ^ index * left ^ (last + 1 - index) *
      ((last + 1).choose index : S)
  have firstTerm : term 0 = left ^ (last + 1) := by
    unfold term
    simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul, mul_one]
  have lastTerm : term (last + 1) = right ^ (last + 1) := by
    unfold term
    simp only [Nat.sub_self, pow_zero, finite_choose_self, Nat.cast_one,
      mul_one]
  have interiorTermZero (index : Nat) (indexBelow : index < last) :
      term (index + 1) = 0 := by
    have castZero : (((last + 1).choose (index + 1) : Nat) : S) = 0 :=
      interiorZero (index + 1) (by omega0) (by omega0)
    unfold term
    rw [castZero, mul_zero]
  have middleSumZero :
      finitePrefixSum last (fun index => term (index + 1)) = 0 := by
    calc
      finitePrefixSum last (fun index => term (index + 1)) =
          finitePrefixSum last (fun _ : Nat => (0 : S)) := by
            apply finitePrefixSum_congr
            intro index indexBelow
            exact interiorTermZero index indexBelow
      _ = 0 := finitePrefixSum_zero_values last
  rw [finite_binomial_theorem]
  unfold finiteBinomialExpansion
  change finitePrefixSum (last + 1 + 1) term = _
  rw [finitePrefixSum_succ_last, finitePrefixSum_succ, firstTerm,
    middleSumZero, lastTerm]
  simp only [add_zero, Nat.succ_eq_add_one]

/-- A positive natural strictly below `p` has nonzero cast in a nontrivial
explicit field of characteristic `p`.  The proof uses the executable extended
Euclidean algorithm: primality makes the two naturals coprime, and their
computed Bezout coefficients would otherwise force `1 = 0`. -/
theorem prime_interior_natCast_ne_zero
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (index : Nat) (indexPositive : index ≠ 0) (indexBelow : index < prime) :
    (index : R) ≠ 0 := by
  intro indexCastZero
  let result := RFAP.CanonicalGCD.compute prime index
  have specification := RFAP.CanonicalGCD.compute_spec prime index
  have gcdEqualsOne : result.gcd = 1 := by
    rcases primeIsPrime.eq_one_or_self_of_dvd result.gcd
        specification.2.1 with equalsOne | equalsPrime
    · exact equalsOne
    · have primeLeIndex : prime ≤ index := by
        rw [← equalsPrime]
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero indexPositive)
          specification.2.2
      exact (Nat.not_le_of_lt indexBelow primeLeIndex).elim
  have bezout := specification.1
  have castBezout := congrArg (fun value : Int => (value : R)) bezout
  have computedGcdEqualsOne :
      (RFAP.CanonicalGCD.compute prime index).gcd = 1 := gcdEqualsOne
  apply oneNonzero
  simpa only [computedGcdEqualsOne, Nat.cast_one, Int.cast_one, Int.cast_add,
    QuotientFreeRing.intCast_mul, Int.cast_natCast, primeCastZero,
    indexCastZero, zero_mul, mul_zero, zero_add]
    using castBezout

/-- Every strictly interior binomial coefficient in a prime row casts to zero
when the prime itself casts to zero.  This proof uses Pascal's finite
multiplicative recurrence and explicit field cancellation; it does not use the
choice-bearing upstream divisibility convenience theorem. -/
theorem prime_interior_choose_cast_zero
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (index : Nat) (indexPositive : index ≠ 0) (indexBelow : index < prime) :
    (prime.choose index : R) = 0 := by
  obtain ⟨last, primeEquation⟩ := Nat.exists_eq_succ_of_ne_zero
    primeIsPrime.ne_zero
  obtain ⟨previous, indexEquation⟩ := Nat.exists_eq_succ_of_ne_zero
    indexPositive
  subst prime
  subst index
  have naturalRecurrence := Nat.add_one_mul_choose_eq last previous
  have castRecurrence := congrArg (fun value : Nat => (value : R))
    naturalRecurrence
  simp only [Nat.cast_mul] at castRecurrence
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
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (left right : R) :
    (left + right) ^ prime = left ^ prime + right ^ prime :=
  add_pow_eq_endpoints_of_interior_choose_cast_zero prime
    primeIsPrime.ne_zero
    (fun index indexPositive indexBelow =>
      prime_interior_choose_cast_zero prime primeIsPrime primeCastZero
        oneNonzero index indexPositive indexBelow)
    left right

/-- Every natural residue label satisfies Frobenius in characteristic `p`.
The induction uses only the finite prime-binomial identity. -/
theorem prime_natCast_pow
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (residue : Nat) :
    (residue : R) ^ prime = (residue : R) := by
  induction residue with
  | zero =>
      simp only [Nat.cast_zero]
      exact zero_pow primeIsPrime.ne_zero
  | succ residue inductionHypothesis =>
      rw [Nat.cast_succ,
        prime_add_pow prime primeIsPrime primeCastZero oneNonzero,
        inductionHypothesis, one_pow]

end RFAP
