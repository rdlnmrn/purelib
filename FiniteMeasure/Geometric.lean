import mathlib.Tactic.QuotientFreeOmega
import FiniteMeasure.Bounds

/-!
# Explicit finite geometric search

This neutral utility turns a positive rational tolerance into a finite index
at which a displayed quarter-power allowance is small enough.  Termination
uses a coefficient-computed binary-length fuel certificate, not a limit or an
Archimedean existence theorem.
-/

namespace FiniteMeasure.Geometric

open FiniteMeasure

/-- Rational allowance with quarter-power decay. -/
def quarterAllowance (scale : Coordinate) (index : Nat) : Coordinate :=
  scale / (4 : Coordinate) ^ index

theorem quarterAllowance_eq_mul_pow (scale : Coordinate) (index : Nat) :
    quarterAllowance scale index =
      scale * (1 / 4 : Coordinate) ^ index := by
  rw [quarterAllowance, RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveFraction.inv_pow_direct,
    RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveFraction.one_mul]

theorem quarterAllowance_nonneg {scale : Coordinate}
    (nonnegative : 0 ≤ scale) (index : Nat) :
    0 ≤ quarterAllowance scale index :=
  RFAP.ConstructiveFraction.div_nonneg_direct nonnegative
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) index)

theorem quarterAllowance_pos {scale : Coordinate} (positive : 0 < scale)
    (index : Nat) : 0 < quarterAllowance scale index :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (RFAP.ConstructiveFraction.pow_pos_direct (by decide) index)

/-- The explicit scan endpoint is below the requested allowance. -/
theorem terminal_quarterAllowance_lt {scale target : Coordinate}
    (scaleNonnegative : 0 ≤ scale) (targetPositive : 0 < target)
    (current : Nat) :
    quarterAllowance scale
        (current +
          (Nat.log2 (RFAP.ConstructiveFraction.ceilNat (scale / target)) + 1)) <
      target := by
  let quotient : Coordinate := scale / target
  let ceiling : Nat := RFAP.ConstructiveFraction.ceilNat quotient
  let fuel : Nat := Nat.log2 ceiling + 1
  let exponent : Nat := current + fuel
  have quotientNonnegative : 0 ≤ quotient :=
    RFAP.ConstructiveFraction.div_nonneg_direct scaleNonnegative
      targetPositive.le
  have quotientLe : quotient ≤ (ceiling : Coordinate) :=
    RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg quotientNonnegative
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
      (2 : Coordinate) ^ exponent := by
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
  have scaled : scale < (4 : Coordinate) ^ exponent * target :=
    (RFAP.ConstructiveFraction.div_lt_iff_pos targetPositive).mp
      quotientLtPower
  change scale / (4 : Coordinate) ^ exponent < target
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos powerPositive).mpr
  simpa only [RFAP.ConstructiveFraction.mul_comm] using scaled

/-- Pure bounded scan for the first successful rational comparison. -/
def scanFirstBelow (scale target : Coordinate) : Nat → Nat → Nat
  | current, 0 => current
  | current, fuel + 1 =>
      if quarterAllowance scale current < target then current
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
      quarterAllowance scale (current + fuel) < target →
        quarterAllowance scale
          (scanFirstBelow scale target current fuel) < target
  | current, 0, terminal => by
      simpa only [Nat.add_zero, scanFirstBelow] using terminal
  | current, fuel + 1, terminal => by
      rw [scanFirstBelow]
      split
      · assumption
      · apply scanFirstBelow_accurate scale target (current + 1) fuel
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using terminal

/-- Transparently computed successful index with finite binary-length fuel. -/
def firstQuarterBelow (scale : Coordinate) (current : Nat)
    (target : Coordinate) : Nat :=
  scanFirstBelow scale target current
    (Nat.log2 (RFAP.ConstructiveFraction.ceilNat (scale / target)) + 1)

theorem firstQuarterBelow_ge (scale : Coordinate) (current : Nat)
    (target : Coordinate) :
    current ≤ firstQuarterBelow scale current target :=
  scanFirstBelow_ge scale target current _

theorem firstQuarterBelow_le (scale : Coordinate) (current : Nat)
    (target : Coordinate) :
    firstQuarterBelow scale current target ≤
      current +
        (Nat.log2 (RFAP.ConstructiveFraction.ceilNat (scale / target)) + 1) :=
  scanFirstBelow_le_add scale target current _

theorem firstQuarterBelow_accurate (scale : Coordinate)
    (scaleNonnegative : 0 ≤ scale) (current : Nat) (target : Coordinate)
    (targetPositive : 0 < target) :
    quarterAllowance scale (firstQuarterBelow scale current target) < target := by
  apply scanFirstBelow_accurate scale target current
  exact terminal_quarterAllowance_lt scaleNonnegative targetPositive current

end FiniteMeasure.Geometric
