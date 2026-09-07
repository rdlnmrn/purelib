import mathlib.Tactic.QuotientFreeOmega
import CCL.Encoding.Normalization
import mathlib.RFAP.ConstructiveFraction

/-!
# Explicit finite geometric refinement

This module turns a positive rational accuracy request into a finite natural
index at which a displayed quarter-power allowance is small enough.  The
search has a coefficient-computed finite fuel certificate.  It stops at the
first successful comparison, and neither its definition nor its proof refers
to a limit, an infinite sequence as an object, or an Archimedean existence
principle.
-/

namespace CCL.FiniteGeometric

abbrev Coordinate := RFAP.ConstructiveFraction.Rational

/-- A rational squared-error allowance with quarter-power decay. -/
def quarterRadius (scale : Coordinate) (index : Nat) : Coordinate :=
  scale / (4 : Coordinate) ^ index

theorem quarterRadius_eq_mul_pow (scale : Coordinate) (index : Nat) :
    quarterRadius scale index = scale * (1 / 4 : Coordinate) ^ index := by
  rw [quarterRadius, RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveFraction.inv_pow_direct,
    RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveFraction.one_mul]

theorem quarterRadius_nonneg {scale : Coordinate} (nonnegative : 0 ≤ scale)
    (index : Nat) :
    0 ≤ quarterRadius scale index := by
  exact RFAP.ConstructiveFraction.div_nonneg_direct nonnegative
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) index)

theorem quarterRadius_pos {scale : Coordinate} (positive : 0 < scale)
    (index : Nat) :
    0 < quarterRadius scale index := by
  exact RFAP.ConstructiveFraction.div_pos_direct positive
    (RFAP.ConstructiveFraction.pow_pos_direct (by decide) index)

theorem quarterRadius_le_scale {scale : Coordinate} (nonnegative : 0 ≤ scale)
    (index : Nat) :
    quarterRadius scale index ≤ scale := by
  rw [quarterRadius_eq_mul_pow]
  have powerBound : (1 / 4 : Coordinate) ^ index ≤ 1 := by
    have bound := RFAP.ConstructiveFraction.pow_le_pow_direct
      (by decide : (0 : Coordinate) ≤ 1 / 4)
      (by decide : (1 / 4 : Coordinate) ≤ 1) index
    simpa only [one_pow] using bound
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    powerBound nonnegative
  simpa only [RFAP.ConstructiveFraction.mul_one_direct] using scaled

/-- Later finite indices have no larger quarter-radius allowance. -/
theorem quarterRadius_antitone {scale : Coordinate}
    (scaleNonnegative : 0 ≤ scale) {earlier later : Nat}
    (order : earlier ≤ later) :
    quarterRadius scale later ≤ quarterRadius scale earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow, pow_add]
  have extraPowerLe : (1 / 4 : Coordinate) ^ extra ≤ 1 := by
    have powerOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      (show (0 : Coordinate) ≤ 1 / 4 by decide)
      (show (1 / 4 : Coordinate) ≤ 1 by decide) extra
    simpa only [one_pow] using powerOrder
  have earlierPowerNonnegative : 0 ≤ (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _
  have scaledNonnegative :
      0 ≤ scale * (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
      earlierPowerNonnegative
  calc
    scale * ((1 / 4 : Coordinate) ^ earlier *
        (1 / 4 : Coordinate) ^ extra) =
      (scale * (1 / 4 : Coordinate) ^ earlier) *
        (1 / 4 : Coordinate) ^ extra := by ring1
    _ ≤ (scale * (1 / 4 : Coordinate) ^ earlier) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        extraPowerLe scaledNonnegative
    _ = scale * (1 / 4 : Coordinate) ^ earlier := by ring1

/-- The explicit scan endpoint is already below the requested allowance.
This is the finite termination certificate used by `firstQuarterResult`. -/
theorem terminal_quarterRadius_lt {scale target : Coordinate}
    (scaleNonnegative : 0 ≤ scale) (targetPositive : 0 < target)
    (current : Nat) :
    quarterRadius scale
        (current +
          (Nat.log2 (RFAP.ConstructiveFraction.ceilNat (scale / target)) + 1)) <
      target := by
  let quotient : Coordinate := scale / target
  let ceiling : Nat := RFAP.ConstructiveFraction.ceilNat quotient
  let fuel : Nat := Nat.log2 ceiling + 1
  let exponent : Nat := current + fuel
  have quotientNonnegative : 0 ≤ quotient := by
    exact RFAP.ConstructiveFraction.div_nonneg_direct scaleNonnegative
      targetPositive.le
  have quotientLe : quotient ≤ (ceiling : Coordinate) := by
    exact RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg
      quotientNonnegative
  have ceilingLtTwoPowNat : ceiling < 2 ^ fuel := by
    simpa only [fuel] using Nat.lt_log2_self (n := ceiling)
  have ceilingLtTwoPow : (ceiling : Coordinate) <
      (2 : Coordinate) ^ fuel := by
    have castBound := RFAP.ConstructiveFraction.natCast_lt_direct
      ceilingLtTwoPowNat
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using castBound
  have quotientLtTwoPow : quotient < (2 : Coordinate) ^ fuel :=
    quotientLe.trans_lt ceilingLtTwoPow
  have fuelLeExponent : fuel ≤ exponent := by
    dsimp only [exponent]
    omega
  have twoPowMonotone : (2 : Coordinate) ^ fuel ≤
      (2 : Coordinate) ^ exponent :=
    by
      have naturalBound : 2 ^ fuel ≤ 2 ^ exponent :=
        Nat.pow_le_pow_right (by decide) fuelLeExponent
      have castBound := RFAP.ConstructiveFraction.natCast_le_direct naturalBound
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using castBound
  have twoPowLeFourPow : (2 : Coordinate) ^ exponent ≤
      (4 : Coordinate) ^ exponent :=
    RFAP.ConstructiveFraction.pow_le_pow_direct (by decide) (by decide) exponent
  have quotientLtPower : quotient < (4 : Coordinate) ^ exponent :=
    quotientLtTwoPow.trans_le (twoPowMonotone.trans twoPowLeFourPow)
  have powerPositive : 0 < (4 : Coordinate) ^ exponent :=
    RFAP.ConstructiveFraction.pow_pos_direct (by decide) exponent
  have scaled : scale < (4 : Coordinate) ^ exponent * target := by
    exact (RFAP.ConstructiveFraction.div_lt_iff_pos targetPositive).mp
      quotientLtPower
  change scale / (4 : Coordinate) ^ exponent < target
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos powerPositive).mpr
  simpa only [RFAP.ConstructiveFraction.mul_comm] using scaled

/-- Pure bounded scan for the first successful rational comparison.  Proof
certificates are deliberately not arguments to this executable function, so
evaluating an index never normalizes a large proof term. -/
def scanFirstBelow (scale target : Coordinate) : Nat → Nat → Nat
  | current, 0 => current
  | current, fuel + 1 =>
      if quarterRadius scale current < target then current
      else scanFirstBelow scale target (current + 1) fuel

theorem scanFirstBelow_ge (scale target : Coordinate) :
    ∀ (current fuel : Nat),
      current ≤ scanFirstBelow scale target current fuel
  | current, 0 => Nat.le_refl current
  | current, fuel + 1 => by
      rw [scanFirstBelow]
      split
      · exact Nat.le_refl current
      · exact (Nat.le_succ current).trans
          (scanFirstBelow_ge scale target (current + 1) fuel)

/-- The bounded scan examines no index beyond its displayed finite fuel. -/
theorem scanFirstBelow_le_add (scale target : Coordinate) :
    ∀ (current fuel : Nat),
      scanFirstBelow scale target current fuel ≤ current + fuel
  | current, 0 => Nat.le_refl current
  | current, fuel + 1 => by
      rw [scanFirstBelow]
      split
      · omega
      · have bound := scanFirstBelow_le_add scale target (current + 1) fuel
        omega

theorem scanFirstBelow_accurate (scale target : Coordinate) :
    ∀ (current fuel : Nat),
      quarterRadius scale (current + fuel) < target →
        quarterRadius scale (scanFirstBelow scale target current fuel) < target
  | current, 0, terminal => by
      simpa only [Nat.add_zero, scanFirstBelow] using terminal
  | current, fuel + 1, terminal => by
      rw [scanFirstBelow]
      split
      · assumption
      · apply scanFirstBelow_accurate scale target (current + 1) fuel
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using terminal

/-- A transparently computed index no smaller than `current`.  Its fuel is
the binary length of one rational ceiling, rather than that ceiling itself. -/
def firstQuarterBelow (scale : Coordinate) (current : Nat)
    (target : Coordinate) : Nat :=
  scanFirstBelow scale target current
    (Nat.log2 (RFAP.ConstructiveFraction.ceilNat (scale / target)) + 1)

theorem firstQuarterBelow_ge (scale : Coordinate) (current : Nat)
    (target : Coordinate) :
    current ≤ firstQuarterBelow scale current target :=
  scanFirstBelow_ge scale target current _

/-- Explicit binary-length upper bound for the accuracy scan. -/
theorem firstQuarterBelow_le (scale : Coordinate) (current : Nat)
    (target : Coordinate) :
    firstQuarterBelow scale current target ≤
      current +
        (Nat.log2 (RFAP.ConstructiveFraction.ceilNat (scale / target)) + 1) :=
  scanFirstBelow_le_add scale target current _

theorem firstQuarterBelow_accurate (scale : Coordinate)
    (scaleNonnegative : 0 ≤ scale) (current : Nat) (target : Coordinate)
    (targetPositive : 0 < target) :
    quarterRadius scale (firstQuarterBelow scale current target) < target := by
  apply scanFirstBelow_accurate scale target current
  exact terminal_quarterRadius_lt scaleNonnegative targetPositive current

/-! ## Finite dyadic square-root under-approximations -/

/-- A positive dyadic rational whose square is found by the bounded
quarter-radius scan.  This is an executable finite substitute for extracting
a real square root when only a rational radius below a positive target is
needed. -/
def dyadicSquareRadius (target : Coordinate) : Coordinate :=
  (1 / 2 : Coordinate) ^ firstQuarterBelow 1 0 target

theorem dyadicSquareRadius_positive (target : Coordinate) :
    0 < dyadicSquareRadius target := by
  unfold dyadicSquareRadius
  exact RFAP.ConstructiveFraction.pow_pos_direct (by decide) _

theorem dyadicSquareRadius_sq_eq (target : Coordinate) :
    dyadicSquareRadius target ^ 2 =
      quarterRadius 1 (firstQuarterBelow 1 0 target) := by
  unfold dyadicSquareRadius
  rw [quarterRadius_eq_mul_pow]
  simp only [RFAP.ConstructiveFraction.one_mul]
  rw [← pow_mul, Nat.mul_comm (firstQuarterBelow 1 0 target) 2,
    pow_mul, show (1 / 2 : Coordinate) ^ 2 = 1 / 4 by decide]

theorem dyadicSquareRadius_sq_lt {target : Coordinate}
    (positive : 0 < target) :
    dyadicSquareRadius target ^ 2 < target := by
  rw [dyadicSquareRadius_sq_eq]
  exact firstQuarterBelow_accurate 1 (by decide) 0 target positive

theorem dyadicSquareRadius_le_one (target : Coordinate) :
    dyadicSquareRadius target <= 1 := by
  unfold dyadicSquareRadius
  have bound := RFAP.ConstructiveFraction.pow_le_pow_direct
    (by decide : (0 : Coordinate) <= 1 / 2)
    (by decide : (1 / 2 : Coordinate) <= 1)
    (firstQuarterBelow 1 0 target)
  simpa only [one_pow] using bound

end CCL.FiniteGeometric
