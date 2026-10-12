module
public import Purelib.NumberTheory.Prime.Basic
import Purelib.Algebra.NatCast
import Purelib.Algebra.Group.Basic
import Purelib.Algebra.Semiring.Normalization
import Purelib.Algebra.Field.ExplicitField

import Purelib.Algebra.Binomial
public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Nat.Choose
import Purelib.Tactic.QuotientFreeOmega
import Purelib.NumberTheory.Prime.Binomial
import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Purelib.Tactic.Ring
import Mathlib.Data.Nat.Prime.Basic

open Purelib.Algebra.Field

open Purelib

open Purelib.Algebra

section
public section

/-!
# Bounded power sums in prime characteristic

All sums in this module range over the explicit natural residue labels
`0, ..., p-1`.  The proofs use finite differences, the project-owned finite
binomial expansion, and explicit field cancellation.  No carrier, primitive
root, or global enumeration is introduced.
-/

namespace Purelib.NumberTheory.Prime.PowerSum

variable {R : Type*} [ExplicitField R]

/-- The bounded sum of the requested natural residue powers. -/
@[expose] def powerSum (prime exponent : Nat) : R :=
  FiniteSum.Prefix.prefixSum prime (fun residue => (residue : R) ^ exponent)

/-- The corresponding bounded powers after the affine centering `x=1-2r`. -/
@[expose] def centeredPowerSum (prime exponent : Nat) : R :=
  FiniteSum.Prefix.prefixSum prime (fun residue =>
    (1 - 2 * (residue : R)) ^ exponent)

/-- A bounded sum of successive power differences telescopes to its explicit
right endpoint. -/
theorem shifted_power_difference_sum
    (count exponent : Nat) (exponentNonzero : exponent ≠ 0) :
    FiniteSum.Prefix.prefixSum count (fun residue =>
        ((residue + 1 : Nat) : R) ^ exponent -
          (residue : R) ^ exponent) =
      (count : R) ^ exponent := by
  induction count with
  | zero =>
      simp only [-eq_self, -iff_self, FiniteSum.Prefix.prefixSum_zero, Nat.cast_zero]
      exact (zero_pow exponentNonzero).symm
  | succ count inductionHypothesis =>
      rw [FiniteSum.Prefix.prefixSum_succ_last]
      rw [inductionHypothesis]
      simp only [-eq_self, -iff_self, NatCast.add, Nat.cast_one]
      generalize (count : R) ^ exponent = currentPower
      generalize ((count : R) + 1) ^ exponent = nextPower
      ring1

/-- The difference `(r+1)^n-r^n` is the explicitly bounded binomial prefix
with its final `r^n` term removed. -/
theorem shifted_power_difference_expansion
    (exponent residue : Nat) :
    (((residue + 1 : Nat) : R) ^ exponent -
        (residue : R) ^ exponent) =
      FiniteSum.Prefix.prefixSum exponent (fun power =>
        (exponent.choose power : R) * (residue : R) ^ power) := open Purelib in by
  let sourceTerm : Nat → R := fun power =>
    (residue : R) ^ power * 1 ^ (exponent - power) *
      (exponent.choose power : R)
  have prefixConversion :
      FiniteSum.Prefix.prefixSum exponent sourceTerm =
        FiniteSum.Prefix.prefixSum exponent (fun power =>
          (exponent.choose power : R) * (residue : R) ^ power) := by
    apply FiniteSum.Prefix.prefixSum_congr
    intro power powerBelow
    unfold sourceTerm
    rw [one_pow]
    generalize (residue : R) ^ power = residuePower
    ring1
  calc
    (((residue + 1 : Nat) : R) ^ exponent -
        (residue : R) ^ exponent) =
      ((1 : R) + (residue : R)) ^ exponent -
        (residue : R) ^ exponent := by
          rw [NatCast.add, Nat.cast_one, add_comm]
    _ = Algebra.Binomial.binomialExpansion exponent (1 : R) (residue : R) -
        (residue : R) ^ exponent := by rw [Algebra.Binomial.binomial_theorem]
    _ = (FiniteSum.Prefix.prefixSum exponent sourceTerm + sourceTerm exponent) -
        (residue : R) ^ exponent := by
          unfold Algebra.Binomial.binomialExpansion sourceTerm
          rw [FiniteSum.Prefix.prefixSum_succ_last]
    _ = FiniteSum.Prefix.prefixSum exponent sourceTerm := by
      unfold sourceTerm
      rw [Nat.sub_self, one_pow, Data.Nat.Choose.choose_self, Nat.cast_one, mul_one]
      generalize (residue : R) ^ exponent = residuePower
      ring1
    _ = FiniteSum.Prefix.prefixSum exponent (fun power =>
        (exponent.choose power : R) * (residue : R) ^ power) :=
      prefixConversion

section
open Purelib.NumberTheory
/-- Summing the finite-difference expansion over all requested residue labels
interchanges two primitive-recursive bounded sums. -/
theorem shifted_power_difference_sum_expansion
    (prime exponent : Nat) :
    FiniteSum.Prefix.prefixSum prime (fun residue =>
        (((residue + 1 : Nat) : R) ^ exponent -
          (residue : R) ^ exponent)) =
      FiniteSum.Prefix.prefixSum exponent (fun power =>
        (exponent.choose power : R) * Prime.PowerSum.powerSum prime power) := by
  calc
    FiniteSum.Prefix.prefixSum prime (fun residue =>
        (((residue + 1 : Nat) : R) ^ exponent -
          (residue : R) ^ exponent)) =
      FiniteSum.Prefix.prefixSum prime (fun residue =>
        FiniteSum.Prefix.prefixSum exponent (fun power =>
          (exponent.choose power : R) * (residue : R) ^ power)) := by
            apply FiniteSum.Prefix.prefixSum_congr
            intro residue residueBelow
            exact Prime.PowerSum.shifted_power_difference_expansion exponent residue
    _ = FiniteSum.Prefix.prefixSum exponent (fun power =>
        FiniteSum.Prefix.prefixSum prime (fun residue =>
          (exponent.choose power : R) * (residue : R) ^ power)) :=
      FiniteSum.Prefix.prefixSum_swap prime exponent _
    _ = FiniteSum.Prefix.prefixSum exponent (fun power =>
        (exponent.choose power : R) * Prime.PowerSum.powerSum prime power) := by
          apply FiniteSum.Prefix.prefixSum_congr
          intro power powerBelow
          unfold Prime.PowerSum.powerSum
          exact FiniteSum.Prefix.prefixSum_mul_left prime
            (exponent.choose power : R) _

/-- Every power sum strictly below the Fermat exponent `p-1` vanishes.  The
proof is finite induction on the exponent using the next binomial finite
difference; its leading coefficient is explicitly cancelled because it is a
nonzero natural cast below `p`. -/
theorem prime_power_sum_zero_below
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (exponent : Nat) (exponentBelow : exponent < prime - 1) :
    Prime.PowerSum.powerSum (R := R) prime exponent = 0 := open Purelib in open Purelib.NumberTheory in by
  revert exponentBelow
  refine Nat.strong_induction_on exponent ?_
  intro exponent inductionHypothesis exponentBelow
  by_cases exponentZero : exponent = 0
  · rw [exponentZero]
    unfold Prime.PowerSum.powerSum
    calc
      FiniteSum.Prefix.prefixSum prime (fun residue => (residue : R) ^ 0) =
          FiniteSum.Prefix.prefixSum prime (fun _ : Nat => (1 : R)) := by
            apply FiniteSum.Prefix.prefixSum_congr
            intro residue residueBelow
            exact pow_zero (residue : R)
      _ = (prime : R) := FiniteSum.Prefix.prefixSum_one prime
      _ = 0 := primeCastZero
  · have nextNonzero : exponent + 1 ≠ 0 := by omega0
    have nextBelowPrime : exponent + 1 < prime := by omega0
    have telescoping := Prime.PowerSum.shifted_power_difference_sum
      (R := R) prime (exponent + 1) nextNonzero
    rw [primeCastZero, zero_pow nextNonzero] at telescoping
    have expansion := Prime.PowerSum.shifted_power_difference_sum_expansion
      (R := R) prime (exponent + 1)
    rw [expansion] at telescoping
    have earlierZero :
        FiniteSum.Prefix.prefixSum exponent (fun power =>
          ((exponent + 1).choose power : R) *
            Prime.PowerSum.powerSum prime power) = 0 := by
      calc
        FiniteSum.Prefix.prefixSum exponent (fun power =>
            ((exponent + 1).choose power : R) *
              Prime.PowerSum.powerSum prime power) =
          FiniteSum.Prefix.prefixSum exponent (fun _ : Nat => (0 : R)) := by
            apply FiniteSum.Prefix.prefixSum_congr
            intro power powerBelow
            rw [inductionHypothesis power powerBelow (by omega0), mul_zero]
        _ = 0 := FiniteSum.Prefix.prefixSum_zero_values exponent
    rw [FiniteSum.Prefix.prefixSum_succ_last, earlierZero, zero_add,
      Data.Nat.Choose.choose_succ_self_right]
      at telescoping
    have nextCastNonzero : ((exponent + 1 : Nat) : R) ≠ 0 :=
      Prime.Binomial.prime_interior_natCast_ne_zero prime primeIsPrime primeCastZero
        oneNonzero (exponent + 1) nextNonzero nextBelowPrime
    exact ExplicitField.eq_zero_of_mul_eq_zero_left nextCastNonzero telescoping

end

/-- Fermat's power law for one explicitly bounded nonzero residue label. -/
theorem prime_residue_fermat_power
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (residue : Nat) (residuePositive : residue ≠ 0)
    (residueBelow : residue < prime) :
    (residue : R) ^ (prime - 1) = 1 := open Purelib.NumberTheory in by
  have residueCastNonzero : (residue : R) ≠ 0 :=
    Prime.Binomial.prime_interior_natCast_ne_zero prime primeIsPrime primeCastZero
      oneNonzero residue residuePositive residueBelow
  have frobenius : (residue : R) ^ prime = (residue : R) :=
    Prime.Binomial.prime_natCast_pow prime primeIsPrime primeCastZero oneNonzero residue
  have productEquality :
      (residue : R) * (residue : R) ^ (prime - 1) =
        (residue : R) * 1 := by
    calc
      (residue : R) * (residue : R) ^ (prime - 1) =
          (residue : R) ^ (prime - 1 + 1) := by rw [pow_succ, mul_comm]
      _ = (residue : R) ^ prime :=
        congrArg (fun exponent : Nat => (residue : R) ^ exponent)
          (by omega0 : prime - 1 + 1 = prime)
      _ = (residue : R) := frobenius
      _ = (residue : R) * 1 := by rw [mul_one]
  have differenceProduct :
      (residue : R) * ((residue : R) ^ (prime - 1) - 1) = 0 := by
    rw [mul_sub, productEquality, sub_self]
  exact Group.eq_of_sub_eq_zero
    (ExplicitField.eq_zero_of_mul_eq_zero_left residueCastNonzero differenceProduct)

open Purelib.NumberTheory
/-- The Fermat-exponent power sum is `-1`: residue zero contributes zero and
each of the remaining `p-1` explicit labels contributes one. -/
theorem prime_power_sum_fermat
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0) :
    Prime.PowerSum.powerSum (R := R) prime (prime - 1) = -1 := by
  have primeOneLt : 1 < prime := (NumberTheory.Prime.one_lt primeIsPrime)
  have primePredPositive : prime - 1 ≠ 0 := by
    omega0
  have primeAsSucc : prime = (prime - 1) + 1 := by omega0
  have tailOnes :
      FiniteSum.Prefix.prefixSum (prime - 1) (fun index =>
          ((index + 1 : Nat) : R) ^ (prime - 1)) =
        FiniteSum.Prefix.prefixSum (prime - 1) (fun _ : Nat => (1 : R)) := by
    apply FiniteSum.Prefix.prefixSum_congr
    intro index indexBelow
    exact Prime.PowerSum.prime_residue_fermat_power prime primeIsPrime primeCastZero
      oneNonzero (index + 1) (by omega0) (by omega0)
  have predecessorCast : ((prime - 1 : Nat) : R) = -1 := by
    have castEquation := congrArg (fun value : Nat => (value : R)) primeAsSucc
    simp only [-eq_self, -iff_self, NatCast.add, Nat.cast_one] at castEquation
    calc
      ((prime - 1 : Nat) : R) = (prime : R) - 1 := by
        rw [castEquation]
        ring1
      _ = -1 := by rw [primeCastZero]; ring1
  unfold Prime.PowerSum.powerSum
  rw [primeAsSucc, FiniteSum.Prefix.prefixSum_succ]
  rw [show prime - 1 + 1 - 1 = prime - 1 by omega0]
  simp only [-eq_self, -iff_self, Nat.cast_zero]
  change (0 : R) ^ (prime - 1) +
      FiniteSum.Prefix.prefixSum (prime - 1) (fun index =>
        ((index + 1 : Nat) : R) ^ (prime - 1)) = -1
  rw [zero_pow primePredPositive, zero_add, tailOnes,
    FiniteSum.Prefix.prefixSum_one, predecessorCast]

/-- Above the Fermat exponent but below twice it, every explicit residue
power reduces by exactly `p-1`. -/
theorem prime_residue_power_reduce_once
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (residue exponent reduced : Nat) (residueBelow : residue < prime)
    (exponentEquation : exponent = (prime - 1) + reduced)
    (exponentNonzero : exponent ≠ 0) (reducedNonzero : reduced ≠ 0) :
    (residue : R) ^ exponent = (residue : R) ^ reduced := by
  rcases residue with _ | residue
  · rw [Nat.cast_zero, zero_pow exponentNonzero, zero_pow reducedNonzero]
  · rw [exponentEquation, pow_add,
      Prime.PowerSum.prime_residue_fermat_power prime primeIsPrime primeCastZero oneNonzero
        (residue + 1) (by omega0) residueBelow,
      one_mul]

/-- Every power sum from `p` through `2p-4` vanishes after one explicit
Fermat reduction to an exponent strictly below `p-1`. -/
theorem prime_power_sum_zero_above
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (exponent : Nat) (primeAtMost : prime ≤ exponent)
    (exponentAtMost : exponent ≤ prime + prime - 4) :
    Prime.PowerSum.powerSum (R := R) prime exponent = 0 := by
  have primePositive : 0 < prime := (NumberTheory.Prime.pos primeIsPrime)
  let reduced := exponent - (prime - 1)
  have exponentEquation : exponent = (prime - 1) + reduced := by
    unfold reduced
    omega0
  have exponentNonzero : exponent ≠ 0 := by omega0
  have reducedNonzero : reduced ≠ 0 := by
    unfold reduced
    omega0
  have reducedBelow : reduced < prime - 1 := by
    unfold reduced
    omega0
  calc
    Prime.PowerSum.powerSum (R := R) prime exponent =
        Prime.PowerSum.powerSum prime reduced := by
          unfold Prime.PowerSum.powerSum
          apply FiniteSum.Prefix.prefixSum_congr
          intro residue residueBelow
          exact Prime.PowerSum.prime_residue_power_reduce_once prime primeIsPrime
            primeCastZero oneNonzero residue exponent reduced residueBelow
            exponentEquation exponentNonzero reducedNonzero
    _ = 0 := Prime.PowerSum.prime_power_sum_zero_below prime primeIsPrime primeCastZero
      oneNonzero reduced reducedBelow

/-- Expanding each centered residue power and interchanging the two bounded
sums expresses it through the ordinary residue power sums. -/
theorem centered_power_sum_expansion
    (prime exponent : Nat) :
    Prime.PowerSum.centeredPowerSum (R := R) prime exponent =
      FiniteSum.Prefix.prefixSum (exponent + 1) (fun power =>
        (-2 : R) ^ power * (exponent.choose power : R) *
          Prime.PowerSum.powerSum prime power) := open Purelib in by
  let term : Nat → Nat → R := fun residue power =>
    (-2 : R) ^ power * (exponent.choose power : R) *
      (residue : R) ^ power
  have pointwise (residue : Nat) :
      (1 - 2 * (residue : R)) ^ exponent =
        FiniteSum.Prefix.prefixSum (exponent + 1) (term residue) := by
    calc
      (1 - 2 * (residue : R)) ^ exponent =
          ((1 : R) + (-2 * (residue : R))) ^ exponent := by
        exact congrArg (fun value : R => value ^ exponent) (by ring1)
      _ = Algebra.Binomial.binomialExpansion exponent 1
          (-2 * (residue : R)) := by rw [Algebra.Binomial.binomial_theorem]
      _ = FiniteSum.Prefix.prefixSum (exponent + 1) (term residue) := by
        unfold Algebra.Binomial.binomialExpansion term
        apply FiniteSum.Prefix.prefixSum_congr
        intro power powerBelow
        rw [one_pow, Semiring.Normalization.product_pow]
        generalize (-2 : R) ^ power = signPower
        generalize (residue : R) ^ power = residuePower
        ring1
  unfold Prime.PowerSum.centeredPowerSum
  calc
    FiniteSum.Prefix.prefixSum prime (fun residue =>
        (1 - 2 * (residue : R)) ^ exponent) =
      FiniteSum.Prefix.prefixSum prime (fun residue =>
        FiniteSum.Prefix.prefixSum (exponent + 1) (term residue)) := by
          apply FiniteSum.Prefix.prefixSum_congr
          intro residue residueBelow
          exact pointwise residue
    _ = FiniteSum.Prefix.prefixSum (exponent + 1) (fun power =>
        FiniteSum.Prefix.prefixSum prime (fun residue => term residue power)) :=
      FiniteSum.Prefix.prefixSum_swap prime (exponent + 1) term
    _ = FiniteSum.Prefix.prefixSum (exponent + 1) (fun power =>
        (-2 : R) ^ power * (exponent.choose power : R) *
          Prime.PowerSum.powerSum prime power) := by
            apply FiniteSum.Prefix.prefixSum_congr
            intro power powerBelow
            unfold term Prime.PowerSum.powerSum
            exact FiniteSum.Prefix.prefixSum_mul_left prime
              ((-2 : R) ^ power * (exponent.choose power : R)) _

/-- Centered powers below `p-1` have zero bounded residue sum. -/
theorem prime_centered_power_sum_zero_below
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (exponent : Nat) (exponentBelow : exponent < prime - 1) :
    Prime.PowerSum.centeredPowerSum (R := R) prime exponent = 0 := by
  rw [Prime.PowerSum.centered_power_sum_expansion]
  calc
    FiniteSum.Prefix.prefixSum (exponent + 1) (fun power =>
        (-2 : R) ^ power * (exponent.choose power : R) *
          Prime.PowerSum.powerSum prime power) =
      FiniteSum.Prefix.prefixSum (exponent + 1) (fun _ : Nat => (0 : R)) := by
        apply FiniteSum.Prefix.prefixSum_congr
        intro power powerBelow
        rw [Prime.PowerSum.prime_power_sum_zero_below prime primeIsPrime primeCastZero
          oneNonzero power (by omega0), mul_zero]
    _ = 0 := FiniteSum.Prefix.prefixSum_zero_values (exponent + 1)

/-- The centered Fermat-exponent power sum is also `-1`; the affine scale
contributes `(-2)^(p-1)=1`. -/
theorem prime_centered_power_sum_fermat
    (prime : Nat) (primeIsPrime : NumberTheory.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (twoNonzero : (2 : R) ≠ 0) :
    Prime.PowerSum.centeredPowerSum (R := R) prime (prime - 1) = -1 := open Purelib in by
  have primeNotTwo : prime ≠ 2 := by
    intro primeEqualsTwo
    apply twoNonzero
    simpa only [-eq_self, -iff_self, primeEqualsTwo, Nat.cast_ofNat] using primeCastZero
  have twoBelow : 2 < prime := by
    have twoAtMost := (NumberTheory.Prime.two_le primeIsPrime)
    omega0
  have twoFermat : (2 : R) ^ (prime - 1) = 1 := by
    simpa only [-eq_self, -iff_self, Nat.cast_ofNat] using
      (Prime.PowerSum.prime_residue_fermat_power prime primeIsPrime primeCastZero
        oneNonzero 2 (by decide) twoBelow :
        ((2 : Nat) : R) ^ (prime - 1) = 1)
  have predecessorEven : ∃ half : Nat, prime - 1 = half + half := by
    rcases (NumberTheory.Prime.odd_of_ne_two primeIsPrime) primeNotTwo with ⟨half, equation⟩
    exact ⟨half, by omega0⟩
  have negativeTwoFermat : (-2 : R) ^ (prime - 1) = 1 := by
    obtain ⟨half, equation⟩ := predecessorEven
    have negativeEven (half : Nat) :
        (-2 : R) ^ (half + half) = (2 : R) ^ (half + half) := by
      induction half with
      | zero => rw [pow_zero, pow_zero]
      | succ half ih =>
          have next : (half + 1) + (half + 1) = (half + half) + 1 + 1 := by omega0
          rw [next]
          calc
            (-2 : R) ^ ((half + half) + 1 + 1) =
                ((-2 : R) ^ (half + half) * -2) * -2 := by
              rw [pow_succ, pow_succ]
            _ = ((2 : R) ^ (half + half) * -2) * -2 :=
              congrArg (fun value : R => (value * -2) * -2) ih
            _ = (2 : R) ^ (half + half) * (2 * 2) := by
              generalize (2 : R) ^ (half + half) = evenPower
              ring1
            _ = (2 : R) ^ ((half + half) + 1 + 1) := by
              rw [pow_succ, pow_succ, mul_assoc]
    exact (congrArg (fun exponent : Nat => (-2 : R) ^ exponent) equation).trans
      ((negativeEven half).trans
        ((congrArg (fun exponent : Nat => (2 : R) ^ exponent) equation).symm.trans twoFermat))
  clear predecessorEven
  have exponentSucc : prime - 1 + 1 = prime := by omega0
  rw [Prime.PowerSum.centered_power_sum_expansion]
  rw [exponentSucc, show prime = (prime - 1) + 1 by omega0,
    FiniteSum.Prefix.prefixSum_succ_last]
  rw [show prime - 1 + 1 - 1 = prime - 1 by omega0,
    show prime - 1 + 1 = prime by omega0]
  have earlierZero :
      FiniteSum.Prefix.prefixSum (prime - 1) (fun power =>
        (-2 : R) ^ power * ((prime - 1).choose power : R) *
          Prime.PowerSum.powerSum prime power) = 0 := by
    calc
      FiniteSum.Prefix.prefixSum (prime - 1) (fun power =>
          (-2 : R) ^ power * ((prime - 1).choose power : R) *
            Prime.PowerSum.powerSum prime power) =
        FiniteSum.Prefix.prefixSum (prime - 1) (fun _ : Nat => (0 : R)) := by
          apply FiniteSum.Prefix.prefixSum_congr
          intro power powerBelow
          rw [Prime.PowerSum.prime_power_sum_zero_below prime primeIsPrime primeCastZero
            oneNonzero power powerBelow, mul_zero]
      _ = 0 := FiniteSum.Prefix.prefixSum_zero_values (prime - 1)
  rw [earlierZero, zero_add, Data.Nat.Choose.choose_self, Nat.cast_one,
    Prime.PowerSum.prime_power_sum_fermat prime primeIsPrime primeCastZero oneNonzero,
    negativeTwoFermat]
  ring1

end Purelib.NumberTheory.Prime.PowerSum

end
