import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadChebyshev
import mathlib.RFAP.PrimePowerSum

/-!
# Finite prime-residue Chebyshev sums

This module proves the bounded moment calculation needed for Exercise 8.11.
It treats a Chebyshev value through its two-step recurrence and ordinary
centered residue powers; no polynomial completion or field enumeration is
used.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The explicitly bounded centered Chebyshev moment
`sum_r (1-2r)^a T_n(1-2r)`. -/
def finiteCenteredChebyshevMoment
    (prime power index : Nat) : K :=
  RFAP.finitePrefixSum prime (fun residue =>
    (1 - 2 * (residue : K)) ^ power *
      chebyshevFirst index (1 - 2 * (residue : K)))

/-- The zeroth moment, i.e. the bounded sum of Chebyshev values. -/
def finiteCenteredChebyshevSum (prime index : Nat) : K :=
  finiteCenteredChebyshevMoment prime 0 index

/-- The zeroth-moment wrapper is exactly the explicitly bounded sum of the
requested Chebyshev values. -/
theorem finiteCenteredChebyshevSum_eq_prefix
    (prime index : Nat) :
    finiteCenteredChebyshevSum (K := K) prime index =
      RFAP.finitePrefixSum prime (fun residue =>
        chebyshevFirst index (1 - 2 * (residue : K))) := by
  unfold finiteCenteredChebyshevSum finiteCenteredChebyshevMoment
  apply RFAP.finitePrefixSum_congr
  intro residue residueBelow
  rw [pow_zero, one_mul]

@[simp] theorem finiteCenteredChebyshevMoment_zero
    (prime power : Nat) :
    finiteCenteredChebyshevMoment (K := K) prime power 0 =
      RFAP.finiteCenteredPowerSum prime power := by
  unfold finiteCenteredChebyshevMoment RFAP.finiteCenteredPowerSum
  apply RFAP.finitePrefixSum_congr
  intro residue residueBelow
  rw [chebyshevFirst_zero, mul_one]

@[simp] theorem finiteCenteredChebyshevMoment_one
    (prime power : Nat) :
    finiteCenteredChebyshevMoment (K := K) prime power 1 =
      RFAP.finiteCenteredPowerSum prime (power + 1) := by
  unfold finiteCenteredChebyshevMoment RFAP.finiteCenteredPowerSum
  apply RFAP.finitePrefixSum_congr
  intro residue residueBelow
  rw [chebyshevFirst_one, ← pow_succ]

/-- The Chebyshev recurrence lifts directly to bounded centered moments. -/
theorem finiteCenteredChebyshevMoment_recurrence
    (prime power index : Nat) :
    finiteCenteredChebyshevMoment (K := K) prime power (index + 2) =
      2 * finiteCenteredChebyshevMoment prime (power + 1) (index + 1) -
        finiteCenteredChebyshevMoment prime power index := by
  unfold finiteCenteredChebyshevMoment
  calc
    RFAP.finitePrefixSum prime (fun residue =>
        (1 - 2 * (residue : K)) ^ power *
          chebyshevFirst (index + 2) (1 - 2 * (residue : K))) =
      RFAP.finitePrefixSum prime (fun residue =>
        2 * ((1 - 2 * (residue : K)) ^ (power + 1) *
          chebyshevFirst (index + 1) (1 - 2 * (residue : K))) -
        ((1 - 2 * (residue : K)) ^ power *
          chebyshevFirst index (1 - 2 * (residue : K)))) := by
            apply RFAP.finitePrefixSum_congr
            intro residue residueBelow
            rw [chebyshevFirst_succ_succ, pow_succ]
            ring1
    _ = RFAP.finitePrefixSum prime (fun residue =>
          2 * ((1 - 2 * (residue : K)) ^ (power + 1) *
            chebyshevFirst (index + 1) (1 - 2 * (residue : K)))) -
        RFAP.finitePrefixSum prime (fun residue =>
          (1 - 2 * (residue : K)) ^ power *
            chebyshevFirst index (1 - 2 * (residue : K))) := by
              rw [RFAP.finitePrefixSum_sub]
    _ = 2 * RFAP.finitePrefixSum prime (fun residue =>
          (1 - 2 * (residue : K)) ^ (power + 1) *
            chebyshevFirst (index + 1) (1 - 2 * (residue : K))) -
        RFAP.finitePrefixSum prime (fun residue =>
          (1 - 2 * (residue : K)) ^ power *
            chebyshevFirst index (1 - 2 * (residue : K))) := by
              rw [RFAP.finitePrefixSum_mul_left]

/-- Every centered Chebyshev moment of total degree below `p-1` vanishes. -/
theorem prime_centered_chebyshev_moment_zero
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (power index : Nat) (totalBelow : power + index < prime - 1) :
    finiteCenteredChebyshevMoment (K := K) prime power index = 0 := by
  induction index using Nat.strong_induction_on generalizing power with
  | h index inductionHypothesis =>
      rcases index with _ | _ | index
      · rw [finiteCenteredChebyshevMoment_zero]
        exact RFAP.prime_centered_power_sum_zero_below prime primeIsPrime
          primeCastZero oneNonzero power (by omega0)
      · rw [finiteCenteredChebyshevMoment_one]
        exact RFAP.prime_centered_power_sum_zero_below prime primeIsPrime
          primeCastZero oneNonzero (power + 1) (by omega0)
      · rw [finiteCenteredChebyshevMoment_recurrence]
        rw [inductionHypothesis (index + 1) (by omega0) (power + 1) (by omega0),
          inductionHypothesis index (by omega0) power (by omega0)]
        ring1

/-- On the boundary of total degree `p-1`, the moment is the leading
Chebyshev coefficient times the centered Fermat sum. -/
theorem prime_centered_chebyshev_moment_boundary
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (power index : Nat) (totalEquation : power + index = prime - 1) :
    finiteCenteredChebyshevMoment (K := K) prime power index =
      -(2 : K) ^ (index - 1) := by
  induction index using Nat.strong_induction_on generalizing power with
  | h index inductionHypothesis =>
      rcases index with _ | _ | index
      · rw [finiteCenteredChebyshevMoment_zero]
        rw [show power = prime - 1 by omega0,
          RFAP.prime_centered_power_sum_fermat prime primeIsPrime
            primeCastZero oneNonzero twoNonzero]
        simp only [Nat.zero_sub, pow_zero]
      · rw [finiteCenteredChebyshevMoment_one]
        rw [show power + 1 = prime - 1 by omega0,
          RFAP.prime_centered_power_sum_fermat prime primeIsPrime
            primeCastZero oneNonzero twoNonzero]
        simp only [Nat.add_sub_cancel, pow_zero]
      · rw [finiteCenteredChebyshevMoment_recurrence]
        rw [inductionHypothesis (index + 1) (by omega0) (power + 1) (by omega0),
          prime_centered_chebyshev_moment_zero prime primeIsPrime
            primeCastZero oneNonzero power index (by omega0)]
        rw [show index + 1 - 1 = index by omega0,
          show index + 2 - 1 = index + 1 by omega0, pow_succ]
        ring1

/-- The zeroth Chebyshev sum vanishes for every requested index below the
Fermat boundary `p-1`. -/
theorem prime_centered_chebyshev_sum_zero
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (index : Nat) (indexBelow : index < prime - 1) :
    finiteCenteredChebyshevSum (K := K) prime index = 0 := by
  unfold finiteCenteredChebyshevSum
  exact prime_centered_chebyshev_moment_zero prime primeIsPrime
    primeCastZero oneNonzero 0 index (by omega0)

/-- At the Fermat boundary, twice the bounded Chebyshev sum is `-1`.  This
division-free form is the one needed in the two exceptional cases of
Exercise 8.11. -/
theorem prime_centered_chebyshev_sum_boundary_cleared
    (prime : Nat) (primeIsPrime : Nat.Prime prime)
    (primeCastZero : (prime : K) = 0) (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    2 * finiteCenteredChebyshevSum (K := K) prime (prime - 1) = -1 := by
  have twoBelow : 2 < prime := by
    have primeNotTwo : prime ≠ 2 := by
      intro primeEqualsTwo
      apply twoNonzero
      simpa only [primeEqualsTwo, Nat.cast_ofNat] using primeCastZero
    have twoAtMost := primeIsPrime.two_le
    omega0
  have twoFermat : (2 : K) ^ (prime - 1) = 1 := by
    simpa only [Nat.cast_ofNat] using
      (RFAP.prime_residue_fermat_power prime primeIsPrime primeCastZero
        oneNonzero 2 (by decide) twoBelow :
        ((2 : Nat) : K) ^ (prime - 1) = 1)
  have boundary := prime_centered_chebyshev_moment_boundary
    (K := K) prime primeIsPrime primeCastZero oneNonzero twoNonzero
      0 (prime - 1) (by omega0)
  unfold finiteCenteredChebyshevSum
  rw [boundary]
  have predecessorPositive : 0 < prime - 1 := by
    have := primeIsPrime.one_lt
    omega0
  rw [show prime - 1 = (prime - 2) + 1 by omega0, pow_succ] at twoFermat
  calc
    2 * (-(2 : K) ^ (prime - 1 - 1)) =
        -((2 : K) ^ (prime - 2) * 2) := by
          rw [show prime - 1 - 1 = prime - 2 by omega0]
          ring1
    _ = -1 := by rw [twoFermat]

/-- Summing the subtraction-free product-to-sum identity over the requested
residue labels.  The ordering hypothesis is only natural-number bookkeeping;
no order is used in the coefficient field. -/
theorem finiteCenteredChebyshev_product_sum
    (prime first second : Nat) (firstAtMostSecond : first ≤ second) :
    2 * RFAP.finitePrefixSum prime (fun residue =>
        chebyshevFirst first (1 - 2 * (residue : K)) *
          chebyshevFirst second (1 - 2 * (residue : K))) =
      finiteCenteredChebyshevSum (K := K) prime (first + second) +
        finiteCenteredChebyshevSum prime (second - first) := by
  let center : Nat → K := fun residue => 1 - 2 * (residue : K)
  have pointwise (residue : Nat) :
      2 * (chebyshevFirst first (center residue) *
          chebyshevFirst second (center residue)) =
        chebyshevFirst (first + second) (center residue) +
          chebyshevFirst (second - first) (center residue) := by
    have product := chebyshevFirst_product_add_sub
      (K := K) (second - first) first (center residue)
    rw [show second - first + first = second by omega0] at product
    calc
      2 * (chebyshevFirst first (center residue) *
          chebyshevFirst second (center residue)) =
        2 * chebyshevFirst second (center residue) *
          chebyshevFirst first (center residue) := by ring1
      _ = chebyshevFirst (first + second) (center residue) +
          chebyshevFirst (second - first) (center residue) := by
            simpa only [Nat.add_comm] using product
  rw [show 2 * RFAP.finitePrefixSum prime (fun residue =>
      chebyshevFirst first (1 - 2 * (residue : K)) *
        chebyshevFirst second (1 - 2 * (residue : K))) =
      RFAP.finitePrefixSum prime (fun residue =>
        2 * (chebyshevFirst first (center residue) *
          chebyshevFirst second (center residue))) by
        exact (RFAP.finitePrefixSum_mul_left prime 2 _).symm]
  calc
    RFAP.finitePrefixSum prime (fun residue =>
        2 * (chebyshevFirst first (center residue) *
          chebyshevFirst second (center residue))) =
      RFAP.finitePrefixSum prime (fun residue =>
        chebyshevFirst (first + second) (center residue) +
          chebyshevFirst (second - first) (center residue)) := by
            apply RFAP.finitePrefixSum_congr
            intro residue residueBelow
            exact pointwise residue
    _ = RFAP.finitePrefixSum prime (fun residue =>
          chebyshevFirst (first + second) (center residue)) +
        RFAP.finitePrefixSum prime (fun residue =>
          chebyshevFirst (second - first) (center residue)) := by
            rw [RFAP.finitePrefixSum_add]
    _ = finiteCenteredChebyshevSum (K := K) prime (first + second) +
        finiteCenteredChebyshevSum prime (second - first) := by
          rw [finiteCenteredChebyshevSum_eq_prefix,
            finiteCenteredChebyshevSum_eq_prefix]

end DivineProportions
