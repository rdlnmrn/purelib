import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.Normalization
import mathlib.RFAP.ConstructiveFraction

/-!
# Finite dyadic normalization of a positive constructive fraction

For one displayed positive rational, a bounded binary scan finds a dyadic
scaling into the deliberately interior interval `[3/4,3/2]`.  The scan fuel
is the computed rational ceiling (or the ceiling of the reciprocal), so this
module contains no unbounded search or Archimedean existence principle.
-/

namespace CCL.PositiveDyadic

abbrev Coordinate := RFAP.ConstructiveFraction.Rational

inductive Direction where
  | down
  | up
deriving DecidableEq, Repr

def power (exponent : Nat) : Coordinate := (2 : Coordinate) ^ exponent

def factor : Direction → Nat → Coordinate
  | .down, exponent => 1 / power exponent
  | .up, exponent => power exponent

def normalized (value : Coordinate) : Direction → Nat → Coordinate
  | .down, exponent => value / power exponent
  | .up, exponent => power exponent * value

private def powerPredicate (value : Coordinate) (exponent : Nat) : Prop :=
  value ≤ power exponent

private instance (value : Coordinate) (exponent : Nat) :
    Decidable (powerPredicate value exponent) := by
  unfold powerPredicate
  infer_instance

/-- The first binary power at least a positive displayed rational. -/
def powerCeiling (value : Coordinate) (positive : 0 < value) :
    CCL.Normalization.FirstResult (powerPredicate value) 0 := by
  let fuel := RFAP.ConstructiveFraction.ceilNat value
  have valueLeFuel : value ≤ (fuel : Coordinate) :=
    RFAP.ConstructiveFraction.le_natCast_ceilNat_of_nonneg positive.le
  have fuelLePowerNat : fuel ≤ 2 ^ fuel :=
    (Nat.le_succ fuel).trans
      (CCL.Normalization.succ_le_two_pow fuel)
  have fuelLePower : (fuel : Coordinate) ≤ power fuel := by
    have cast := RFAP.ConstructiveFraction.natCast_le_direct fuelLePowerNat
    simpa only [power, Nat.cast_pow, Nat.cast_ofNat] using cast
  apply CCL.Normalization.scanFirst
    (powerPredicate value) (fun _ => inferInstance) 0 fuel
  simpa only [Nat.zero_add, powerPredicate] using valueLeFuel.trans fuelLePower

theorem powerCeiling_upper (value : Coordinate) (positive : 0 < value) :
    value ≤ power (powerCeiling value positive).exponent :=
  (powerCeiling value positive).holds

theorem powerCeiling_previous_lt (value : Coordinate) (positive : 0 < value)
    (previous : Nat)
    (exponentEq : (powerCeiling value positive).exponent = previous + 1) :
    power previous < value := by
  have failure := (powerCeiling value positive).before_fails previous
    (Nat.zero_le previous) (by
      calc
        previous < previous + 1 := Nat.lt_succ_self previous
        _ = (powerCeiling value positive).exponent := exponentEq.symm)
  exact lt_of_not_ge (by
    simpa only [powerPredicate] using failure)

private theorem power_pos (exponent : Nat) : 0 < power exponent :=
  RFAP.ConstructiveFraction.pow_pos_direct (by decide) exponent

theorem factor_pos (direction : Direction) (exponent : Nat) :
    0 < factor direction exponent := by
  cases direction with
  | down =>
      exact RFAP.ConstructiveFraction.div_pos_direct (by decide)
        (power_pos exponent)
  | up => exact power_pos exponent

theorem normalized_eq_factor_mul (value : Coordinate)
    (direction : Direction) (exponent : Nat) :
    normalized value direction exponent = factor direction exponent * value := by
  cases direction with
  | down =>
      change value * (power exponent)⁻¹ =
        (1 * (power exponent)⁻¹) * value
      rw [RFAP.ConstructiveFraction.one_mul,
        RFAP.ConstructiveFraction.mul_comm]
  | up => rfl

private theorem power_succ (exponent : Nat) :
    power (exponent + 1) = power exponent * 2 := by
  rw [power, power, pow_succ]

private theorem div_one_direct (value : Coordinate) : value / 1 = value := by
  change value * (1 : Coordinate)⁻¹ = value
  rw [show (1 : Coordinate)⁻¹ = 1 by decide,
    RFAP.ConstructiveFraction.mul_one_direct]

private theorem down_previous_eq_two_down (value : Coordinate)
    (exponent : Nat) :
    normalized value .down exponent =
      2 * normalized value .down (exponent + 1) := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (power_pos exponent).ne'
  calc
    normalized value .down exponent * power exponent = value :=
      RFAP.ConstructiveFraction.div_mul_cancel_of_ne value _
        (power_pos exponent).ne'
    _ = normalized value .down (exponent + 1) * power (exponent + 1) :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne value _
        (power_pos (exponent + 1)).ne').symm
    _ = (2 * normalized value .down (exponent + 1)) *
        power exponent := by
      rw [power_succ]
      ring1

private theorem up_succ_eq_two_up (value : Coordinate) (exponent : Nat) :
    normalized value .up (exponent + 1) =
      2 * normalized value .up exponent := by
  rw [normalized, normalized, power_succ]
  ring1

/-- A finite dyadic scaling with a uniform rational margin from both local
logarithm chart boundaries. -/
structure Normalization (value : Coordinate) where
  direction : Direction
  exponent : Nat
  lower : 3 / 4 ≤ normalized value direction exponent
  upper : normalized value direction exponent ≤ 3 / 2

private def normalizeHigh (value : Coordinate) (positive : 0 < value)
    (oneLe : 1 ≤ value) : Normalization value := by
  let ceiling := powerCeiling value positive
  let exponent := ceiling.exponent
  have baseUpper : normalized value .down exponent ≤ 1 := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (power_pos exponent)).2
    simpa only [powerPredicate, exponent,
      RFAP.ConstructiveFraction.one_mul] using ceiling.holds
  have baseHalf : 1 / 2 < normalized value .down exponent := by
    cases exponentIdentity : exponent with
    | zero =>
        have normalizedEq : normalized value .down 0 = value := by
          rw [normalized, power, pow_zero]
          exact div_one_direct value
        rw [normalizedEq]
        exact (by decide : (1 / 2 : Coordinate) < 1).trans_le oneLe
    | succ previous =>
        have previousLt : power previous < value := by
          exact powerCeiling_previous_lt value positive previous
            (by simpa only [exponent, Nat.succ_eq_add_one] using exponentIdentity)
        rw [normalized]
        apply (RFAP.ConstructiveFraction.lt_div_iff_pos
          (power_pos (previous + 1))).2
        calc
          (1 / 2 : Coordinate) * power (previous + 1) = power previous := by
            rw [power_succ]
            have halfTimesTwo : (1 / 2 : Coordinate) * 2 = 1 :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 2 (by decide)
            calc
              (1 / 2 : Coordinate) * (power previous * 2) =
                  ((1 / 2 : Coordinate) * 2) * power previous := by ring1
              _ = power previous := by
                rw [halfTimesTwo, RFAP.ConstructiveFraction.one_mul]
          _ < value := previousLt
  if robust : 3 / 4 ≤ normalized value .down exponent then
    exact
      { direction := .down
        exponent := exponent
        lower := robust
        upper := baseUpper.trans (by decide) }
  else
    have baseLt : normalized value .down exponent < 3 / 4 :=
      lt_of_not_ge robust
    cases exponentIdentity : exponent with
    | zero =>
        have baseOne : 1 ≤ normalized value .down exponent := by
          rw [exponentIdentity, normalized, power, pow_zero,
            div_one_direct]
          exact oneLe
        exact ((not_lt_of_ge baseOne) (baseLt.trans (by decide))).elim
    | succ previous =>
        have relation : normalized value .down previous =
            2 * normalized value .down exponent := by
          rw [exponentIdentity]
          exact down_previous_eq_two_down value previous
        refine
          { direction := .down
            exponent := previous
            lower := ?_
            upper := ?_ }
        · rw [relation]
          have scaled :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              (by decide : (0 : Coordinate) < 2) baseHalf
          exact (by decide : (3 / 4 : Coordinate) < 2 * (1 / 2)).le.trans
            scaled.le
        · rw [relation]
          have scaled :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              (by decide : (0 : Coordinate) < 2) baseLt
          calc
            2 * normalized value .down exponent ≤ 2 * (3 / 4) := scaled.le
            _ = 3 / 2 := by decide

private def normalizeLow (value : Coordinate) (positive : 0 < value)
    (ltOne : value < 1) : Normalization value := by
  let inverse := value⁻¹
  have inversePositive : 0 < inverse :=
    RFAP.ConstructiveFraction.inv_pos_direct positive
  let ceiling := powerCeiling inverse inversePositive
  let exponent := ceiling.exponent
  have inverseGtOne : 1 < inverse := by
    calc
      1 < 1 / value := by
        apply (RFAP.ConstructiveFraction.lt_div_iff_pos positive).2
        simpa only [RFAP.ConstructiveFraction.one_mul] using ltOne
      _ = inverse := by
        dsimp only [inverse]
        change 1 * value⁻¹ = value⁻¹
        exact RFAP.ConstructiveFraction.one_mul _
  have exponentPositive : 0 < exponent := by
    cases exponentIdentity : exponent with
    | zero =>
        have inverseLeOne : inverse ≤ 1 := by
          simpa only [powerPredicate, exponent, exponentIdentity,
            power, pow_zero] using
            ceiling.holds
        exact ((not_lt_of_ge inverseLeOne) inverseGtOne).elim
    | succ previous => exact Nat.succ_pos previous
  cases exponentIdentity : exponent with
  | zero => exact (Nat.not_lt_zero 0 (by simpa only [exponentIdentity] using
      exponentPositive)).elim
  | succ previous =>
      have previousLt : power previous < inverse :=
        powerCeiling_previous_lt inverse inversePositive previous (by
          simpa only [exponent, Nat.succ_eq_add_one] using exponentIdentity)
      have baseLower : 1 ≤ normalized value .up exponent := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (show inverse ≤ power exponent from by
              simpa only [powerPredicate, exponent] using ceiling.holds)
            positive.le
        have cancellation : inverse * value = 1 :=
          RFAP.ConstructiveFraction.inv_mul_cancel value positive.ne'
        calc
          1 = inverse * value := cancellation.symm
          _ ≤ power exponent * value := scaled
          _ = normalized value .up exponent := rfl
      have previousUpper : normalized value .up previous < 1 := by
        have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          previousLt positive
        have cancellation : inverse * value = 1 := by
          dsimp only [inverse]
          exact RFAP.ConstructiveFraction.inv_mul_cancel value positive.ne'
        rw [cancellation] at scaled
        exact scaled
      have baseUpper : normalized value .up exponent < 2 := by
        have relation : normalized value .up exponent =
            2 * normalized value .up previous := by
          rw [exponentIdentity]
          exact up_succ_eq_two_up value previous
        rw [relation]
        have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
          (by decide : (0 : Coordinate) < 2) previousUpper
        simpa only [RFAP.ConstructiveFraction.mul_one_direct] using scaled
      if robust : normalized value .up exponent ≤ 3 / 2 then
        exact
          { direction := .up
            exponent := exponent
            lower :=
              (by decide : (3 / 4 : Coordinate) ≤ 1).trans baseLower
            upper := robust }
      else
        have baseLt : 3 / 2 < normalized value .up exponent :=
          lt_of_not_ge robust
        have relation : normalized value .up exponent =
            2 * normalized value .up previous := by
          rw [exponentIdentity]
          exact up_succ_eq_two_up value previous
        refine
          { direction := .up
            exponent := previous
            lower := ?_
            upper := previousUpper.le.trans (by decide) }
        rw [relation] at baseLt
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := (2 : Coordinate))
        · calc
            (3 / 4 : Coordinate) * 2 = 3 / 2 := by decide
            _ ≤ 2 * normalized value .up previous := baseLt.le
            _ = normalized value .up previous * 2 :=
              RFAP.ConstructiveFraction.mul_comm _ _
        · decide

/-- Total finite normalization of a displayed positive rational. -/
def normalize (value : Coordinate) (positive : 0 < value) :
    Normalization value :=
  if oneLe : 1 ≤ value then normalizeHigh value positive oneLe
  else normalizeLow value positive (lt_of_not_ge oneLe)

end CCL.PositiveDyadic
