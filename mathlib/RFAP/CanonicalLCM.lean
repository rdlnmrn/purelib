import mathlib.RFAP.CanonicalGCD

/-!
# Certificate-backed least common multiples

This module derives least common multiples from the project's structurally
recursive extended-GCD calculation.  The operation and every theorem below
stay on explicit natural-number data; in particular, none of the upstream
`Nat.gcd` or `Nat.lcm` proof interface is used.
-/

namespace RFAP.CanonicalLCM

/-- The common multiple obtained by removing the certified GCD from the left
input before multiplication. -/
def lcm (leftInput rightInput : Nat) : Nat :=
  leftInput / (RFAP.CanonicalGCD.compute leftInput rightInput).gcd * rightInput

/-- The right input divides the displayed common multiple directly. -/
theorem right_dvd_lcm (leftInput rightInput : Nat) :
    rightInput ∣ lcm leftInput rightInput := by
  refine ⟨leftInput /
    (RFAP.CanonicalGCD.compute leftInput rightInput).gcd, ?_⟩
  unfold lcm
  exact Nat.mul_comm _ _

/-- The left input divides the displayed common multiple.  The witness is the
right input after removal of the same certified GCD. -/
theorem left_dvd_lcm (leftInput rightInput : Nat) :
    leftInput ∣ lcm leftInput rightInput := by
  let result := RFAP.CanonicalGCD.compute leftInput rightInput
  have specification := RFAP.CanonicalGCD.compute_spec leftInput rightInput
  have leftFactorization : leftInput / result.gcd * result.gcd = leftInput :=
    Nat.div_mul_cancel specification.2.1
  have rightFactorization : rightInput / result.gcd * result.gcd = rightInput :=
    Nat.div_mul_cancel specification.2.2
  refine ⟨rightInput / result.gcd, ?_⟩
  change leftInput / result.gcd * rightInput =
    leftInput * (rightInput / result.gcd)
  calc
    leftInput / result.gcd * rightInput =
        leftInput / result.gcd *
          (rightInput / result.gcd * result.gcd) := by
            rw [rightFactorization]
    _ = (leftInput / result.gcd * result.gcd) *
          (rightInput / result.gcd) := by
            rw [Nat.mul_assoc, Nat.mul_comm result.gcd
              (rightInput / result.gcd), ← Nat.mul_assoc]
    _ = leftInput * (rightInput / result.gcd) := by
          rw [leftFactorization]

/-- The constructed common multiple is positive when both inputs are
positive. -/
theorem lcm_pos {leftInput rightInput : Nat}
    (leftPositive : 0 < leftInput) (rightPositive : 0 < rightInput) :
    0 < lcm leftInput rightInput := by
  let result := RFAP.CanonicalGCD.compute leftInput rightInput
  have specification := RFAP.CanonicalGCD.compute_spec leftInput rightInput
  have gcdPositive : 0 < result.gcd :=
    RFAP.CanonicalGCD.compute_gcd_positive_right leftInput rightPositive
  have quotientPositive : 0 < leftInput / result.gcd :=
    Nat.div_pos (Nat.le_of_dvd leftPositive specification.2.1) gcdPositive
  exact Nat.mul_pos quotientPositive rightPositive

/-- Every common multiple of the inputs is divisible by the constructed
multiple.  For a positive right input, the proof factors both inputs by the
certified GCD, cancels that positive common factor, and then applies the
stored Bezout certificate to the two quotients. -/
theorem lcm_dvd {leftInput rightInput commonMultiple : Nat}
    (leftDivides : leftInput ∣ commonMultiple)
    (rightDivides : rightInput ∣ commonMultiple) :
    lcm leftInput rightInput ∣ commonMultiple := by
  cases rightInput with
  | zero =>
      rcases rightDivides with ⟨factor, commonMultipleIdentity⟩
      have commonMultipleZero : commonMultiple = 0 := by
        simpa only [Nat.zero_mul] using commonMultipleIdentity
      rw [commonMultipleZero]
      exact Nat.dvd_zero _
  | succ rightInput =>
      let positiveRight := rightInput + 1
      have rightPositive : 0 < positiveRight := Nat.zero_lt_succ rightInput
      let result := RFAP.CanonicalGCD.compute leftInput positiveRight
      have specification :=
        RFAP.CanonicalGCD.compute_spec leftInput positiveRight
      have gcdPositive : 0 < result.gcd :=
        RFAP.CanonicalGCD.compute_gcd_positive_right leftInput rightPositive
      let leftQuotient := leftInput / result.gcd
      let rightQuotient := positiveRight / result.gcd
      have leftFactorization : leftQuotient * result.gcd = leftInput :=
        Nat.div_mul_cancel specification.2.1
      have rightFactorization : rightQuotient * result.gcd = positiveRight :=
        Nat.div_mul_cancel specification.2.2
      rcases rightDivides with ⟨rightFactor, commonMultipleIdentity⟩
      have commonMultipleFactored :
          commonMultiple = (rightQuotient * rightFactor) * result.gcd := by
        calc
          commonMultiple = positiveRight * rightFactor :=
            commonMultipleIdentity
          _ = (rightQuotient * result.gcd) * rightFactor := by
            rw [rightFactorization]
          _ = (rightQuotient * rightFactor) * result.gcd := by
            rw [Nat.mul_assoc, Nat.mul_comm result.gcd rightFactor,
              ← Nat.mul_assoc]
      have quotientProductDivides :
          leftQuotient * result.gcd ∣
            (rightQuotient * rightFactor) * result.gcd := by
        rw [leftFactorization, ← commonMultipleFactored]
        exact leftDivides
      have leftQuotientDividesProduct :
          leftQuotient ∣ rightQuotient * rightFactor :=
        Nat.dvd_of_mul_dvd_mul_right gcdPositive quotientProductDivides
      have certificate :=
        RFAP.CanonicalGCD.quotientCoprimeCertificate leftInput rightPositive
      have leftQuotientDividesFactor : leftQuotient ∣ rightFactor :=
        certificate.dvd_of_dvd_mul_right (by
          simpa only [Nat.mul_comm] using leftQuotientDividesProduct)
      rcases leftQuotientDividesFactor with
        ⟨finalFactor, rightFactorIdentity⟩
      refine ⟨finalFactor, ?_⟩
      change commonMultiple =
        (leftQuotient * positiveRight) * finalFactor
      calc
        commonMultiple = positiveRight * rightFactor :=
          commonMultipleIdentity
        _ = positiveRight * (leftQuotient * finalFactor) := by
          rw [rightFactorIdentity]
        _ = (leftQuotient * positiveRight) * finalFactor := by
          rw [← Nat.mul_assoc, Nat.mul_comm positiveRight leftQuotient]

/-- The constructed LCM divides the unreduced product of its inputs. -/
theorem lcm_dvd_mul (leftInput rightInput : Nat) :
    lcm leftInput rightInput ∣ leftInput * rightInput :=
  lcm_dvd (Nat.dvd_mul_right leftInput rightInput)
    (Nat.dvd_mul_left rightInput leftInput)

/-- Removing a common factor from an input paired with one changes nothing. -/
theorem lcm_one_right (leftInput : Nat) : lcm leftInput 1 = leftInput := by
  let result := RFAP.CanonicalGCD.compute leftInput 1
  have gcdDividesOne : result.gcd ∣ 1 :=
    (RFAP.CanonicalGCD.compute_spec leftInput 1).2.2
  have gcdEqualsOne : result.gcd = 1 :=
    Nat.eq_one_of_dvd_one gcdDividesOne
  change leftInput / result.gcd * 1 = leftInput
  rw [gcdEqualsOne, Nat.div_one, Nat.mul_one]

end RFAP.CanonicalLCM
