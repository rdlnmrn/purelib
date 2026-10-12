module
import Purelib.Data.Nat.GCD.Coprime
import Purelib.Data.Nat.GCD.Extended

public import Purelib.Data.Nat.GCD.Scalar
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Multiplication

open Purelib.Data.Nat

open Purelib.Data.Nat.GCD

public section

/-!
# Certificate-backed least common multiples

This module derives least common multiples from the project's structurally
recursive scalar-GCD calculation, certified by extended Euclid.  The operation and every theorem below
stay on explicit natural-number data; in particular, none of the upstream
`Nat.gcd` or `Nat.lcm` proof interface is used.
-/

namespace Purelib.Data.Nat.LCM

open Purelib.Data.Nat

/-- Compute a common multiple after cancelling the scalar gcd from the left input.

The exposed calculation is leftInput / gcd leftInput rightInput times rightInput. The
divisibility theorems establish that this value is the least common multiple,
including zero inputs. -/
@[expose] def lcm (leftInput rightInput : Nat) : Nat :=
  leftInput / Scalar.gcd leftInput rightInput * rightInput

/-- The right input divides the displayed common multiple directly. -/
theorem right_dvd_lcm (leftInput rightInput : Nat) :
    rightInput ∣ LCM.lcm leftInput rightInput := by
  refine ⟨leftInput /
    Scalar.gcd leftInput rightInput, ?_⟩
  unfold LCM.lcm
  exact Nat.mul_comm _ _

/-- The left input divides the displayed common multiple.

The witness is the right input after removal of the same certified GCD. -/
theorem left_dvd_lcm (leftInput rightInput : Nat) :
    leftInput ∣ LCM.lcm leftInput rightInput := by
  unfold LCM.lcm
  rw [Scalar.gcd_eq_compute]
  let result := Extended.compute leftInput rightInput
  have specification := Extended.compute_spec leftInput rightInput
  have leftFactorization : leftInput / result.gcd * result.gcd = leftInput :=
    Division.div_mul_cancel specification.2.1
  have rightFactorization : rightInput / result.gcd * result.gcd = rightInput :=
    Division.div_mul_cancel specification.2.2
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
            rw [Multiplication.mul_assoc, Nat.mul_comm result.gcd
              (rightInput / result.gcd), ← Multiplication.mul_assoc]
    _ = leftInput * (rightInput / result.gcd) := by
          rw [leftFactorization]

/-- The constructed common multiple is positive when both inputs are positive. -/
theorem lcm_pos {leftInput rightInput : Nat}
    (leftPositive : 0 < leftInput) (rightPositive : 0 < rightInput) :
    0 < LCM.lcm leftInput rightInput := by
  unfold LCM.lcm
  rw [Scalar.gcd_eq_compute]
  let result := Extended.compute leftInput rightInput
  have specification := Extended.compute_spec leftInput rightInput
  have gcdPositive : 0 < result.gcd :=
    Extended.compute_gcd_positive_right leftInput rightPositive
  have quotientPositive : 0 < leftInput / result.gcd :=
    Division.div_pos (Divisibility.le_of_dvd leftPositive specification.2.1) gcdPositive
  exact Nat.mul_pos quotientPositive rightPositive

/-- Every common multiple of the inputs is divisible by the constructed multiple.

For a positive right input, the proof factors both inputs by the certified GCD,
cancels that positive common factor, and then applies the stored Bezout certificate
to the two quotients. -/
theorem lcm_dvd {leftInput rightInput commonMultiple : Nat}
    (leftDivides : leftInput ∣ commonMultiple)
    (rightDivides : rightInput ∣ commonMultiple) :
    LCM.lcm leftInput rightInput ∣ commonMultiple := by
  unfold LCM.lcm
  rw [Scalar.gcd_eq_compute]
  cases rightInput with
  | zero =>
      rcases rightDivides with ⟨factor, commonMultipleIdentity⟩
      have commonMultipleZero : commonMultiple = 0 :=
        commonMultipleIdentity.trans (Nat.zero_mul factor)
      rw [commonMultipleZero]
      exact Divisibility.zero _
  | succ rightInput =>
      let positiveRight := rightInput + 1
      have rightPositive : 0 < positiveRight := Nat.zero_lt_succ rightInput
      let result := Extended.compute leftInput positiveRight
      have specification :=
        Extended.compute_spec leftInput positiveRight
      have gcdPositive : 0 < result.gcd :=
        Extended.compute_gcd_positive_right leftInput rightPositive
      let leftQuotient := leftInput / result.gcd
      let rightQuotient := positiveRight / result.gcd
      have leftFactorization : leftQuotient * result.gcd = leftInput :=
        Division.div_mul_cancel specification.2.1
      have rightFactorization : rightQuotient * result.gcd = positiveRight :=
        Division.div_mul_cancel specification.2.2
      rcases rightDivides with ⟨rightFactor, commonMultipleIdentity⟩
      have commonMultipleFactored :
          commonMultiple = (rightQuotient * rightFactor) * result.gcd := by
        calc
          commonMultiple = positiveRight * rightFactor :=
            commonMultipleIdentity
          _ = (rightQuotient * result.gcd) * rightFactor := by
            rw [rightFactorization]
          _ = (rightQuotient * rightFactor) * result.gcd := by
            rw [Multiplication.mul_assoc, Nat.mul_comm result.gcd rightFactor,
              ← Multiplication.mul_assoc]
      have quotientProductDivides :
          leftQuotient * result.gcd ∣
            (rightQuotient * rightFactor) * result.gcd := by
        rw [leftFactorization, ← commonMultipleFactored]
        exact leftDivides
      have leftQuotientDividesProduct :
          leftQuotient ∣ rightQuotient * rightFactor :=
        Divisibility.of_mul_dvd_mul_right gcdPositive quotientProductDivides
      have certificate :=
        Coprime.quotientCoprimeCertificate leftInput rightPositive
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
          rw [← Multiplication.mul_assoc, Nat.mul_comm positiveRight leftQuotient]

/-- The constructed LCM divides the unreduced product of its inputs. -/
theorem lcm_dvd_mul (leftInput rightInput : Nat) :
    LCM.lcm leftInput rightInput ∣ leftInput * rightInput :=
  LCM.lcm_dvd ⟨rightInput, rfl⟩
    ⟨leftInput, Nat.mul_comm leftInput rightInput⟩

/-- Removing a common factor from an input paired with one changes nothing. -/
theorem lcm_one_right (leftInput : Nat) : LCM.lcm leftInput 1 = leftInput := by
  unfold LCM.lcm
  rw [Scalar.gcd_eq_compute]
  let result := Extended.compute leftInput 1
  have gcdDividesOne : result.gcd ∣ 1 :=
    (Extended.compute_spec leftInput 1).2.2
  have gcdEqualsOne : result.gcd = 1 :=
    Divisibility.eq_one_of_dvd_one gcdDividesOne
  change leftInput / result.gcd * 1 = leftInput
  rw [gcdEqualsOne, Division.div_one, Nat.mul_one]

end Purelib.Data.Nat.LCM
