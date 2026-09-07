import mathlib.Tactic.QuotientFreeOmega
import mathlib.RFAP.PrimeBinomial

/-!
# Bounded power sums in prime characteristic

All sums in this module range over the explicit natural residue labels
`0, ..., p-1`.  The proofs use finite differences, the project-owned finite
binomial expansion, and explicit field cancellation.  No carrier, primitive
root, or global enumeration is introduced.
-/

namespace RFAP

variable {R : Type*} [ExplicitField R]

/-- The bounded sum of the requested natural residue powers. -/
def finitePowerSum (prime exponent : Nat) : R :=
  finitePrefixSum prime (fun residue => (residue : R) ^ exponent)

/-- The corresponding bounded powers after the affine centering `x=1-2r`. -/
def finiteCenteredPowerSum (prime exponent : Nat) : R :=
  finitePrefixSum prime (fun residue =>
    (1 - 2 * (residue : R)) ^ exponent)

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : R} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have factorCancel : factor * factor⁻¹ = (1 : R) :=
    ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by rw [one_mul]
    _ = (factor * factor⁻¹) * value := by rw [factorCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

/-- A bounded sum of successive power differences telescopes to its explicit
right endpoint. -/
theorem finite_shifted_power_difference
    (count exponent : Nat) (exponentNonzero : exponent ≠ 0) :
    finitePrefixSum count (fun residue =>
        ((residue + 1 : Nat) : R) ^ exponent -
          (residue : R) ^ exponent) =
      (count : R) ^ exponent := by
  induction count with
  | zero =>
      simp only [finitePrefixSum_zero, Nat.cast_zero]
      exact (zero_pow exponentNonzero).symm
  | succ count inductionHypothesis =>
      rw [finitePrefixSum_succ_last]
      rw [inductionHypothesis]
      simp only [Nat.cast_add, Nat.cast_one]
      ring1

/-- The difference `(r+1)^n-r^n` is the explicitly bounded binomial prefix
with its final `r^n` term removed. -/
theorem shifted_power_difference_expansion
    (exponent residue : Nat) :
    (((residue + 1 : Nat) : R) ^ exponent -
        (residue : R) ^ exponent) =
      finitePrefixSum exponent (fun power =>
        (exponent.choose power : R) * (residue : R) ^ power) := by
  let sourceTerm : Nat → R := fun power =>
    (residue : R) ^ power * 1 ^ (exponent - power) *
      (exponent.choose power : R)
  have prefixConversion :
      finitePrefixSum exponent sourceTerm =
        finitePrefixSum exponent (fun power =>
          (exponent.choose power : R) * (residue : R) ^ power) := by
    apply finitePrefixSum_congr
    intro power powerBelow
    unfold sourceTerm
    rw [one_pow]
    ring1
  calc
    (((residue + 1 : Nat) : R) ^ exponent -
        (residue : R) ^ exponent) =
      ((1 : R) + (residue : R)) ^ exponent -
        (residue : R) ^ exponent := by
          rw [Nat.cast_add, Nat.cast_one, add_comm]
    _ = finiteBinomialExpansion exponent (1 : R) (residue : R) -
        (residue : R) ^ exponent := by rw [finite_binomial_theorem]
    _ = (finitePrefixSum exponent sourceTerm + sourceTerm exponent) -
        (residue : R) ^ exponent := by
          unfold finiteBinomialExpansion sourceTerm
          rw [finitePrefixSum_succ_last]
    _ = finitePrefixSum exponent sourceTerm := by
      unfold sourceTerm
      rw [Nat.sub_self, one_pow, finite_choose_self, Nat.cast_one, mul_one]
      ring1
    _ = finitePrefixSum exponent (fun power =>
        (exponent.choose power : R) * (residue : R) ^ power) :=
      prefixConversion

/-- Summing the finite-difference expansion over all requested residue labels
interchanges two primitive-recursive bounded sums. -/
theorem finite_shifted_power_difference_expansion
    (prime exponent : Nat) :
    finitePrefixSum prime (fun residue =>
        (((residue + 1 : Nat) : R) ^ exponent -
          (residue : R) ^ exponent)) =
      finitePrefixSum exponent (fun power =>
        (exponent.choose power : R) * finitePowerSum prime power) := by
  calc
    finitePrefixSum prime (fun residue =>
        (((residue + 1 : Nat) : R) ^ exponent -
          (residue : R) ^ exponent)) =
      finitePrefixSum prime (fun residue =>
        finitePrefixSum exponent (fun power =>
          (exponent.choose power : R) * (residue : R) ^ power)) := by
            apply finitePrefixSum_congr
            intro residue residueBelow
            exact shifted_power_difference_expansion exponent residue
    _ = finitePrefixSum exponent (fun power =>
        finitePrefixSum prime (fun residue =>
          (exponent.choose power : R) * (residue : R) ^ power)) :=
      finitePrefixSum_swap prime exponent _
    _ = finitePrefixSum exponent (fun power =>
        (exponent.choose power : R) * finitePowerSum prime power) := by
          apply finitePrefixSum_congr
          intro power powerBelow
          unfold finitePowerSum
          exact finitePrefixSum_mul_left prime
            (exponent.choose power : R) _

/-- Every power sum strictly below the Fermat exponent `p-1` vanishes.  The
proof is finite induction on the exponent using the next binomial finite
difference; its leading coefficient is explicitly cancelled because it is a
nonzero natural cast below `p`. -/
theorem prime_power_sum_zero_below
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (exponent : Nat) (exponentBelow : exponent < prime - 1) :
    finitePowerSum (R := R) prime exponent = 0 := by
  revert exponentBelow
  refine Nat.strong_induction_on exponent ?_
  intro exponent inductionHypothesis exponentBelow
  by_cases exponentZero : exponent = 0
  · rw [exponentZero]
    unfold finitePowerSum
    calc
      finitePrefixSum prime (fun residue => (residue : R) ^ 0) =
          finitePrefixSum prime (fun _ : Nat => (1 : R)) := by
            apply finitePrefixSum_congr
            intro residue residueBelow
            exact pow_zero (residue : R)
      _ = (prime : R) := finitePrefixSum_one prime
      _ = 0 := primeCastZero
  · have nextNonzero : exponent + 1 ≠ 0 := by omega0
    have nextBelowPrime : exponent + 1 < prime := by omega0
    have telescoping := finite_shifted_power_difference
      (R := R) prime (exponent + 1) nextNonzero
    rw [primeCastZero, zero_pow nextNonzero] at telescoping
    have expansion := finite_shifted_power_difference_expansion
      (R := R) prime (exponent + 1)
    rw [expansion] at telescoping
    have earlierZero :
        finitePrefixSum exponent (fun power =>
          ((exponent + 1).choose power : R) *
            finitePowerSum prime power) = 0 := by
      calc
        finitePrefixSum exponent (fun power =>
            ((exponent + 1).choose power : R) *
              finitePowerSum prime power) =
          finitePrefixSum exponent (fun _ : Nat => (0 : R)) := by
            apply finitePrefixSum_congr
            intro power powerBelow
            rw [inductionHypothesis power powerBelow (by omega0), mul_zero]
        _ = 0 := finitePrefixSum_zero_values exponent
    rw [finitePrefixSum_succ_last, earlierZero, zero_add,
      finite_choose_succ_self_right]
      at telescoping
    have nextCastNonzero : ((exponent + 1 : Nat) : R) ≠ 0 :=
      prime_interior_natCast_ne_zero prime primeIsPrime primeCastZero
        oneNonzero (exponent + 1) nextNonzero nextBelowPrime
    exact eq_zero_of_mul_eq_zero_left nextCastNonzero telescoping

/-- Fermat's power law for one explicitly bounded nonzero residue label. -/
theorem prime_residue_fermat_power
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (residue : Nat) (residuePositive : residue ≠ 0)
    (residueBelow : residue < prime) :
    (residue : R) ^ (prime - 1) = 1 := by
  have residueCastNonzero : (residue : R) ≠ 0 :=
    prime_interior_natCast_ne_zero prime primeIsPrime primeCastZero
      oneNonzero residue residuePositive residueBelow
  have frobenius : (residue : R) ^ prime = (residue : R) :=
    prime_natCast_pow prime primeIsPrime primeCastZero oneNonzero residue
  have productEquality :
      (residue : R) * (residue : R) ^ (prime - 1) =
        (residue : R) * 1 := by
    calc
      (residue : R) * (residue : R) ^ (prime - 1) =
          (residue : R) ^ (prime - 1 + 1) := by rw [pow_succ']
      _ = (residue : R) ^ prime := by
        congr 1
        omega0
      _ = (residue : R) := frobenius
      _ = (residue : R) * 1 := by rw [mul_one]
  have differenceProduct :
      (residue : R) * ((residue : R) ^ (prime - 1) - 1) = 0 := by
    rw [mul_sub, productEquality, sub_self]
  exact sub_eq_zero.mp
    (eq_zero_of_mul_eq_zero_left residueCastNonzero differenceProduct)

/-- The Fermat-exponent power sum is `-1`: residue zero contributes zero and
each of the remaining `p-1` explicit labels contributes one. -/
theorem prime_power_sum_fermat
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0) :
    finitePowerSum (R := R) prime (prime - 1) = -1 := by
  have primeOneLt : 1 < prime := primeIsPrime.one_lt
  have primePredPositive : prime - 1 ≠ 0 := by
    omega0
  have primeAsSucc : prime = (prime - 1) + 1 := by omega0
  have tailOnes :
      finitePrefixSum (prime - 1) (fun index =>
          ((index + 1 : Nat) : R) ^ (prime - 1)) =
        finitePrefixSum (prime - 1) (fun _ : Nat => (1 : R)) := by
    apply finitePrefixSum_congr
    intro index indexBelow
    exact prime_residue_fermat_power prime primeIsPrime primeCastZero
      oneNonzero (index + 1) (by omega0) (by omega0)
  have predecessorCast : ((prime - 1 : Nat) : R) = -1 := by
    have castEquation := congrArg (fun value : Nat => (value : R)) primeAsSucc
    simp only [Nat.cast_add, Nat.cast_one] at castEquation
    calc
      ((prime - 1 : Nat) : R) = (prime : R) - 1 := by
        rw [castEquation]
        ring1
      _ = -1 := by rw [primeCastZero]; ring1
  unfold finitePowerSum
  rw [primeAsSucc, finitePrefixSum_succ]
  rw [show prime - 1 + 1 - 1 = prime - 1 by omega0]
  simp only [Nat.cast_zero]
  change (0 : R) ^ (prime - 1) +
      finitePrefixSum (prime - 1) (fun index =>
        ((index + 1 : Nat) : R) ^ (prime - 1)) = -1
  rw [zero_pow primePredPositive, zero_add, tailOnes,
    finitePrefixSum_one, predecessorCast]

/-- Above the Fermat exponent but below twice it, every explicit residue
power reduces by exactly `p-1`. -/
theorem prime_residue_power_reduce_once
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (residue exponent reduced : Nat) (residueBelow : residue < prime)
    (exponentEquation : exponent = (prime - 1) + reduced)
    (exponentNonzero : exponent ≠ 0) (reducedNonzero : reduced ≠ 0) :
    (residue : R) ^ exponent = (residue : R) ^ reduced := by
  rcases residue with _ | residue
  · rw [Nat.cast_zero, zero_pow exponentNonzero, zero_pow reducedNonzero]
  · rw [exponentEquation, pow_add,
      prime_residue_fermat_power prime primeIsPrime primeCastZero oneNonzero
        (residue + 1) (by omega0) residueBelow,
      one_mul]

/-- Every power sum from `p` through `2p-4` vanishes after one explicit
Fermat reduction to an exponent strictly below `p-1`. -/
theorem prime_power_sum_zero_above
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (exponent : Nat) (primeAtMost : prime ≤ exponent)
    (exponentAtMost : exponent ≤ prime + prime - 4) :
    finitePowerSum (R := R) prime exponent = 0 := by
  have primePositive : 0 < prime := primeIsPrime.pos
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
    finitePowerSum (R := R) prime exponent =
        finitePowerSum prime reduced := by
          unfold finitePowerSum
          apply finitePrefixSum_congr
          intro residue residueBelow
          exact prime_residue_power_reduce_once prime primeIsPrime
            primeCastZero oneNonzero residue exponent reduced residueBelow
            exponentEquation exponentNonzero reducedNonzero
    _ = 0 := prime_power_sum_zero_below prime primeIsPrime primeCastZero
      oneNonzero reduced reducedBelow

/-- Expanding each centered residue power and interchanging the two bounded
sums expresses it through the ordinary residue power sums. -/
theorem finite_centered_power_sum_expansion
    (prime exponent : Nat) :
    finiteCenteredPowerSum (R := R) prime exponent =
      finitePrefixSum (exponent + 1) (fun power =>
        (-2 : R) ^ power * (exponent.choose power : R) *
          finitePowerSum prime power) := by
  let term : Nat → Nat → R := fun residue power =>
    (-2 : R) ^ power * (exponent.choose power : R) *
      (residue : R) ^ power
  have pointwise (residue : Nat) :
      (1 - 2 * (residue : R)) ^ exponent =
        finitePrefixSum (exponent + 1) (term residue) := by
    calc
      (1 - 2 * (residue : R)) ^ exponent =
          ((1 : R) + (-2 * (residue : R))) ^ exponent := by
        congr 1
        ring1
      _ = finiteBinomialExpansion exponent 1
          (-2 * (residue : R)) := by rw [finite_binomial_theorem]
      _ = finitePrefixSum (exponent + 1) (term residue) := by
        unfold finiteBinomialExpansion term
        apply finitePrefixSum_congr
        intro power powerBelow
        rw [one_pow, mul_pow]
        ring1
  unfold finiteCenteredPowerSum
  calc
    finitePrefixSum prime (fun residue =>
        (1 - 2 * (residue : R)) ^ exponent) =
      finitePrefixSum prime (fun residue =>
        finitePrefixSum (exponent + 1) (term residue)) := by
          apply finitePrefixSum_congr
          intro residue residueBelow
          exact pointwise residue
    _ = finitePrefixSum (exponent + 1) (fun power =>
        finitePrefixSum prime (fun residue => term residue power)) :=
      finitePrefixSum_swap prime (exponent + 1) term
    _ = finitePrefixSum (exponent + 1) (fun power =>
        (-2 : R) ^ power * (exponent.choose power : R) *
          finitePowerSum prime power) := by
            apply finitePrefixSum_congr
            intro power powerBelow
            unfold term finitePowerSum
            exact finitePrefixSum_mul_left prime
              ((-2 : R) ^ power * (exponent.choose power : R)) _

/-- Centered powers below `p-1` have zero bounded residue sum. -/
theorem prime_centered_power_sum_zero_below
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (exponent : Nat) (exponentBelow : exponent < prime - 1) :
    finiteCenteredPowerSum (R := R) prime exponent = 0 := by
  rw [finite_centered_power_sum_expansion]
  calc
    finitePrefixSum (exponent + 1) (fun power =>
        (-2 : R) ^ power * (exponent.choose power : R) *
          finitePowerSum prime power) =
      finitePrefixSum (exponent + 1) (fun _ : Nat => (0 : R)) := by
        apply finitePrefixSum_congr
        intro power powerBelow
        rw [prime_power_sum_zero_below prime primeIsPrime primeCastZero
          oneNonzero power (by omega0), mul_zero]
    _ = 0 := finitePrefixSum_zero_values (exponent + 1)

/-- The centered Fermat-exponent power sum is also `-1`; the affine scale
contributes `(-2)^(p-1)=1`. -/
theorem prime_centered_power_sum_fermat
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : R) = 0) (oneNonzero : (1 : R) ≠ 0)
    (twoNonzero : (2 : R) ≠ 0) :
    finiteCenteredPowerSum (R := R) prime (prime - 1) = -1 := by
  have primeNotTwo : prime ≠ 2 := by
    intro primeEqualsTwo
    apply twoNonzero
    simpa only [primeEqualsTwo, Nat.cast_ofNat] using primeCastZero
  have twoBelow : 2 < prime := by
    have twoAtMost := primeIsPrime.two_le
    omega0
  have twoFermat : (2 : R) ^ (prime - 1) = 1 := by
    simpa only [Nat.cast_ofNat] using
      (prime_residue_fermat_power prime primeIsPrime primeCastZero
        oneNonzero 2 (by decide) twoBelow :
        ((2 : Nat) : R) ^ (prime - 1) = 1)
  have predecessorEven : Even (prime - 1) := by
    rcases primeIsPrime.odd_of_ne_two primeNotTwo with ⟨half, equation⟩
    exact ⟨half, by omega0⟩
  have negativeTwoFermat : (-2 : R) ^ (prime - 1) = 1 := by
    rw [predecessorEven.neg_pow, twoFermat]
  have exponentSucc : prime - 1 + 1 = prime := by omega0
  rw [finite_centered_power_sum_expansion]
  rw [exponentSucc, show prime = (prime - 1) + 1 by omega0,
    finitePrefixSum_succ_last]
  rw [show prime - 1 + 1 - 1 = prime - 1 by omega0,
    show prime - 1 + 1 = prime by omega0]
  have earlierZero :
      finitePrefixSum (prime - 1) (fun power =>
        (-2 : R) ^ power * ((prime - 1).choose power : R) *
          finitePowerSum prime power) = 0 := by
    calc
      finitePrefixSum (prime - 1) (fun power =>
          (-2 : R) ^ power * ((prime - 1).choose power : R) *
            finitePowerSum prime power) =
        finitePrefixSum (prime - 1) (fun _ : Nat => (0 : R)) := by
          apply finitePrefixSum_congr
          intro power powerBelow
          rw [prime_power_sum_zero_below prime primeIsPrime primeCastZero
            oneNonzero power powerBelow, mul_zero]
      _ = 0 := finitePrefixSum_zero_values (prime - 1)
  rw [earlierZero, zero_add, finite_choose_self, Nat.cast_one,
    prime_power_sum_fermat prime primeIsPrime primeCastZero oneNonzero,
    negativeTwoFermat]
  ring1

end RFAP
