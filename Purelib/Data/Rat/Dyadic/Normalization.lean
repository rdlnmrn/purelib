module
import Purelib.Data.Rat.Fraction.Field.Finite

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Dyadic.Basic
public import Purelib.Data.Rat.Dyadic.PowerCeiling
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat.Fraction.Order

section
public section

/-!
# Finite dyadic normalization of a positive constructive fraction

For one displayed positive rational, a bounded binary scan finds a dyadic
scaling into the deliberately interior interval `[3/4,3/2]`.  The scan fuel
is the computed rational ceiling (or the ceiling of the reciprocal), so this
module contains no unbounded search or Archimedean existence principle.
-/

namespace Purelib.Data.Rat.Dyadic

open Purelib.Data.Rat

-- Preserve this original duplicated nominal/API name; the source formerly suppressed the linter module-wide.
set_option genInjectivity false in
/-- Retain a dyadic direction and exponent that place the original value between three quarters and three halves.

The lower and upper fields certify the scaled value using this same retained direction and exponent. The record keeps
the original rational as its parameter, so its evidence cannot silently refer to another input. -/
structure Normalization (value : Fraction.Rational) where
  /-- The retained choice of upward or downward dyadic scaling. -/ direction : Basic.Direction
  /-- The natural exponent of the retained dyadic factor. -/ exponent : Nat
  /-- Evidence that the scaled original value is at least three quarters. -/ lower : 3 / 4 ≤ Basic.normalized
    value direction exponent
  /-- Evidence that the scaled original value is at most three halves. -/ upper : Basic.normalized value
    direction exponent ≤ 3 / 2

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity Normalization

namespace Normalization

end Normalization
namespace Normalization

/-- Normalize a positive rational at least one by selecting a downward power of two.

Search for the first power of two bounding the value, then use that exponent or its predecessor. The explicit comparison
with three quarters chooses the branch, and both endpoint bounds are retained in the result. -/
private def normalizeHigh (value :
  Fraction.Rational) (positive : 0 < value)
    (oneLe : 1 ≤ value) : Normalization value := by
  let ceiling := PowerCeiling.powerCeiling value positive
  let exponent := ceiling.exponent
  have baseUpper : Basic.normalized value .down exponent ≤ 1 := by
    apply (Field.div_le_iff_pos
      (Basic.power_pos exponent)).2
    simpa only [exponent,
      Fraction.Field.one_mul] using ceiling.holds
  have baseHalf : 1 / 2 < Basic.normalized value .down exponent := by
    cases exponentIdentity : exponent with
    | zero =>
        have normalizedEq : Basic.normalized value .down 0 = value := by
          rw [Basic.normalized, Basic.power, pow_zero]
          exact Fraction.Field.Finite.rational_div_one value
        rw [normalizedEq]
        exact (by decide : (1 / 2 : Fraction.Rational) < 1).trans_le oneLe
    | succ previous =>
        have previousLt : Basic.power previous < value := by
          exact PowerCeiling.powerCeiling_previous_lt value positive previous
            (by simpa only [exponent, Nat.succ_eq_add_one] using exponentIdentity)
        rw [Basic.normalized]
        apply (Field.lt_div_iff_pos
          (Basic.power_pos (previous + 1))).2
        calc
          (1 / 2 : Fraction.Rational) * Basic.power (previous + 1) = Basic.power previous := by
            rw [Basic.power_succ]
            have halfTimesTwo : (1 / 2 : Fraction.Rational) * 2 = 1 :=
              Fraction.Field.div_mul_cancel_of_ne 1 2 (by decide)
            calc
              (1 / 2 : Fraction.Rational) * (Basic.power previous * 2) =
                  ((1 / 2 : Fraction.Rational) * 2) * Basic.power previous := by ring1
              _ = Basic.power previous := by
                rw [halfTimesTwo, Fraction.Field.one_mul]
          _ < value := previousLt
  if robust : 3 / 4 ≤ Basic.normalized value .down exponent then
    exact
      { direction := .down
        exponent := exponent
        lower := robust
        upper := baseUpper.trans (by decide) }
  else
    have baseLt : Basic.normalized value .down exponent < 3 / 4 :=
      lt_of_not_ge robust
    cases exponentIdentity : exponent with
    | zero =>
        have baseOne : 1 ≤ Basic.normalized value .down exponent := by
          rw [exponentIdentity, Basic.normalized, Basic.power, pow_zero,
            Fraction.Field.Finite.rational_div_one]
          exact oneLe
        exact ((not_lt_of_ge baseOne) (baseLt.trans (by decide))).elim
    | succ previous =>
        have relation : Basic.normalized value .down previous =
            2 * Basic.normalized value .down exponent := by
          rw [exponentIdentity]
          exact Basic.down_previous_eq_two_down value previous
        refine
          { direction := .down
            exponent := previous
            lower := ?_
            upper := ?_ }
        · rw [relation]
          have scaled :=
            Arithmetic.mul_lt_mul_of_pos_left_direct
              (by decide : (0 : Fraction.Rational) < 2) baseHalf
          exact (by decide : (3 / 4 : Fraction.Rational) < 2 * (1 / 2)).le.trans
            scaled.le
        · rw [relation]
          have scaled :=
            Arithmetic.mul_lt_mul_of_pos_left_direct
              (by decide : (0 : Fraction.Rational) < 2) baseLt
          calc
            2 * Basic.normalized value .down exponent ≤ 2 * (3 / 4) := scaled.le
            _ = 3 / 2 := by decide

/-- Normalize a positive rational below one by selecting an upward power of two.

Apply the finite power-ceiling search to the positive reciprocal. Compare the upward-scaled value with three halves and
retain either the ceiling exponent or its predecessor, together with the interval bounds. -/
private def normalizeLow (value :
  Fraction.Rational) (positive : 0 < value)
    (ltOne : value < 1) : Normalization value := by
  let inverse := value⁻¹
  have inversePositive : 0 < inverse :=
    Field.inv_pos_direct positive
  let ceiling := PowerCeiling.powerCeiling inverse inversePositive
  let exponent := ceiling.exponent
  have inverseGtOne : 1 < inverse := by
    calc
      1 < 1 / value := by
        apply (Field.lt_div_iff_pos positive).2
        simpa only [Fraction.Field.one_mul] using ltOne
      _ = inverse := by
        dsimp only [inverse]
        change 1 * value⁻¹ = value⁻¹
        exact Fraction.Field.one_mul _
  have exponentPositive : 0 < exponent := by
    cases exponentIdentity : exponent with
    | zero =>
        have inverseLeOne : inverse ≤ 1 := by
          simpa only [exponent, exponentIdentity,
            Basic.power, pow_zero] using
            ceiling.holds
        exact ((not_lt_of_ge inverseLeOne) inverseGtOne).elim
    | succ previous => exact Nat.succ_pos previous
  cases exponentIdentity : exponent with
  | zero => exact (Nat.not_lt_zero 0 (by
      simpa only [exponentIdentity]
        using exponentPositive)).elim
  | succ previous =>
      have previousLt : Basic.power previous < inverse :=
        PowerCeiling.powerCeiling_previous_lt inverse inversePositive previous (by
          simpa only [exponent, Nat.succ_eq_add_one] using exponentIdentity)
      have baseLower : 1 ≤ Basic.normalized value .up exponent := by
        have scaled :=
          Arithmetic.mul_le_mul_of_nonneg_right_direct
            (show inverse ≤ Basic.power exponent from by
              simpa only [exponent] using ceiling.holds)
            positive.le
        have cancellation : inverse * value = 1 :=
          Fraction.Field.inv_mul_cancel value positive.ne'
        calc
          1 = inverse * value := cancellation.symm
          _ ≤ Basic.power exponent * value := scaled
          _ = Basic.normalized value .up exponent := rfl
      have previousUpper : Basic.normalized value .up previous < 1 := by
        have scaled := Arithmetic.mul_lt_mul_of_pos_right_direct
          previousLt positive
        have cancellation : inverse * value = 1 := by
          dsimp only [inverse]
          exact Fraction.Field.inv_mul_cancel value positive.ne'
        rw [cancellation] at scaled
        exact scaled
      have baseUpper : Basic.normalized value .up exponent < 2 := by
        have relation : Basic.normalized value .up exponent =
            2 * Basic.normalized value .up previous := by
          rw [exponentIdentity]
          exact Basic.up_succ_eq_two_up value previous
        rw [relation]
        have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide : (0 : Fraction.Rational) < 2) previousUpper
        simpa only [Fraction.Field.mul_one_direct] using scaled
      if robust : Basic.normalized value .up exponent ≤ 3 / 2 then
        exact
          { direction := .up
            exponent := exponent
            lower :=
              (by decide : (3 / 4 : Fraction.Rational) ≤ 1).trans baseLower
            upper := robust }
      else
        have baseLt : 3 / 2 < Basic.normalized value .up exponent :=
          lt_of_not_ge robust
        have relation : Basic.normalized value .up exponent =
            2 * Basic.normalized value .up previous := by
          rw [exponentIdentity]
          exact Basic.up_succ_eq_two_up value previous
        refine
          { direction := .up
            exponent := previous
            lower := ?_
            upper := previousUpper.le.trans (by decide) }
        rw [relation] at baseLt
        apply Arithmetic.le_of_mul_le_mul_right_direct
          (c := (2 : Fraction.Rational))
        · calc
            (3 / 4 : Fraction.Rational) * 2 = 3 / 2 := by decide
            _ ≤ 2 * Basic.normalized value .up previous := baseLt.le
            _ = Basic.normalized value .up previous * 2 :=
              Fraction.Field.mul_comm _ _
        · decide

/-- Compute certified dyadic normalization of a positive rational into the closed interval from three quarters to three
halves.

Branch on whether the original value is at least one. Each branch computes a finite power ceiling and adjusts its
exponent by at most one; the returned direction and exponent retain both required endpoint inequalities. -/
@[expose] def normalize (value : Fraction.Rational) (positive : 0 < value)
  :
    Normalization value := by
  let powerPositive (exponent : Nat) : 0 <
    Basic.power exponent :=
    Arithmetic.pow_pos_direct (by decide) exponent
  let powerSucc (exponent : Nat) :
      Basic.power (exponent + 1) = Basic.power exponent * 2 := by
    rw [Basic.power, Basic.power, pow_succ]

  let divOne (value : Fraction.Rational) : value
    / 1 = value := by
    change value * (1 : Fraction.Rational)⁻¹ = value
    rw [show (1 : Fraction.Rational)⁻¹ = 1 by decide,
      Fraction.Field.mul_one_direct]

  let downPreviousEqTwoDown (value :
    Fraction.Rational)
      (exponent : Nat) :
      Basic.normalized value .down exponent =
        2 * Basic.normalized value .down (exponent + 1) := by
    apply Fraction.Field.mul_right_cancel_of_ne
      (powerPositive exponent).ne'
    calc
      Basic.normalized value .down exponent * Basic.power exponent = value :=
        Fraction.Field.div_mul_cancel_of_ne value _
          (powerPositive exponent).ne'
      _ = Basic.normalized value .down (exponent + 1) * Basic.power (exponent + 1) :=
        (Fraction.Field.div_mul_cancel_of_ne value _
          (powerPositive (exponent + 1)).ne').symm
      _ = (2 * Basic.normalized value .down (exponent + 1)) *
          Basic.power exponent := by
        rw [powerSucc]
        ring1

  let upSuccEqTwoUp (value : Fraction.Rational)
    (exponent : Nat) :
      Basic.normalized value .up (exponent + 1) =
        2 * Basic.normalized value .up exponent := by
    rw [Basic.normalized, Basic.normalized,
      powerSucc]
    ring1
  let normalizeHigh (value : Fraction.Rational)
    (positive : 0 < value)
      (oneLe : 1 ≤ value) : Normalization value := by
    let ceiling := PowerCeiling.powerCeiling value positive
    let exponent := ceiling.exponent
    have baseUpper : Basic.normalized value .down exponent ≤ 1 := by
      apply (Field.div_le_iff_pos
        (powerPositive exponent)).2
      simpa only [exponent,
        Fraction.Field.one_mul] using ceiling.holds
    have baseHalf : 1 / 2 < Basic.normalized value .down exponent := by
      cases exponentIdentity : exponent with
      | zero =>
          have normalizedEq : Basic.normalized value .down 0 = value := by
            rw [Basic.normalized, Basic.power, pow_zero]
            exact divOne value
          rw [normalizedEq]
          exact (by decide : (1 / 2 : Fraction.Rational) < 1).trans_le oneLe
      | succ previous =>
          have previousLt : Basic.power previous < value := by
            exact PowerCeiling.powerCeiling_previous_lt value positive previous
              (by simpa only [exponent, Nat.succ_eq_add_one] using exponentIdentity)
          rw [Basic.normalized]
          apply (Field.lt_div_iff_pos
            (powerPositive (previous + 1))).2
          calc
            (1 / 2 : Fraction.Rational) * Basic.power (previous + 1) = Basic.power previous := by
              rw [powerSucc]
              have halfTimesTwo : (1 / 2 : Fraction.Rational) * 2 = 1 :=
                Fraction.Field.div_mul_cancel_of_ne 1 2 (by decide)
              calc
                (1 / 2 : Fraction.Rational) * (Basic.power previous * 2) =
                    ((1 / 2 : Fraction.Rational) * 2) * Basic.power previous := by ring1
                _ = Basic.power previous := by
                  rw [halfTimesTwo, Fraction.Field.one_mul]
            _ < value := previousLt
    if robust : 3 / 4 ≤ Basic.normalized value .down exponent then
      exact
        { direction := .down
          exponent := exponent
          lower := robust
          upper := baseUpper.trans (by decide) }
    else
      have baseLt : Basic.normalized value .down exponent < 3 / 4 :=
        lt_of_not_ge robust
      cases exponentIdentity : exponent with
      | zero =>
          have baseOne : 1 ≤ Basic.normalized value .down exponent := by
            rw [exponentIdentity, Basic.normalized, Basic.power, pow_zero,
              divOne]
            exact oneLe
          exact ((not_lt_of_ge baseOne) (baseLt.trans (by decide))).elim
      | succ previous =>
          have relation : Basic.normalized value .down previous =
              2 * Basic.normalized value .down exponent := by
            rw [exponentIdentity]
            exact downPreviousEqTwoDown value
              previous
          refine
            { direction := .down
              exponent := previous
              lower := ?_
              upper := ?_ }
          · rw [relation]
            have scaled :=
              Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide : (0 : Fraction.Rational) < 2) baseHalf
            exact (by decide : (3 / 4 : Fraction.Rational) < 2 * (1 / 2)).le.trans
              scaled.le
          · rw [relation]
            have scaled :=
              Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide : (0 : Fraction.Rational) < 2) baseLt
            calc
              2 * Basic.normalized value .down exponent ≤ 2 * (3 / 4) := scaled.le
              _ = 3 / 2 := by decide
  let normalizeLow (value : Fraction.Rational)
    (positive : 0 < value)
      (ltOne : value < 1) : Normalization value := by
    let inverse := value⁻¹
    have inversePositive : 0 < inverse :=
      Field.inv_pos_direct positive
    let ceiling := PowerCeiling.powerCeiling inverse inversePositive
    let exponent := ceiling.exponent
    have inverseGtOne : 1 < inverse := by
      calc
        1 < 1 / value := by
          apply (Field.lt_div_iff_pos positive).2
          simpa only [Fraction.Field.one_mul] using ltOne
        _ = inverse := by
          dsimp only [inverse]
          change 1 * value⁻¹ = value⁻¹
          exact Fraction.Field.one_mul _
    have exponentPositive : 0 < exponent := by
      cases exponentIdentity : exponent with
      | zero =>
          have inverseLeOne : inverse ≤ 1 := by
            simpa only [exponent, exponentIdentity,
              Basic.power, pow_zero] using
              ceiling.holds
          exact ((not_lt_of_ge inverseLeOne) inverseGtOne).elim
      | succ previous => exact Nat.succ_pos previous
    cases exponentIdentity : exponent with
    | zero => exact (Nat.not_lt_zero 0 (by
        simpa only [exponentIdentity]
          using exponentPositive)).elim
    | succ previous =>
        have previousLt : Basic.power previous < inverse :=
          PowerCeiling.powerCeiling_previous_lt inverse inversePositive previous (by
            simpa only [exponent, Nat.succ_eq_add_one] using exponentIdentity)
        have baseLower : 1 ≤ Basic.normalized value .up exponent := by
          have scaled :=
            Arithmetic.mul_le_mul_of_nonneg_right_direct
              (show inverse ≤ Basic.power exponent from by
                simpa only [exponent] using ceiling.holds)
              positive.le
          have cancellation : inverse * value = 1 :=
            Fraction.Field.inv_mul_cancel value positive.ne'
          calc
            1 = inverse * value := cancellation.symm
            _ ≤ Basic.power exponent * value := scaled
            _ = Basic.normalized value .up exponent := rfl
        have previousUpper : Basic.normalized value .up previous < 1 := by
          have scaled := Arithmetic.mul_lt_mul_of_pos_right_direct
            previousLt positive
          have cancellation : inverse * value = 1 := by
            dsimp only [inverse]
            exact Fraction.Field.inv_mul_cancel value positive.ne'
          rw [cancellation] at scaled
          exact scaled
        have baseUpper : Basic.normalized value .up exponent < 2 := by
          have relation : Basic.normalized value .up exponent =
              2 * Basic.normalized value .up previous := by
            rw [exponentIdentity]
            exact upSuccEqTwoUp value previous
          rw [relation]
          have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct
            (by decide : (0 : Fraction.Rational) < 2) previousUpper
          simpa only [Fraction.Field.mul_one_direct] using scaled
        if robust : Basic.normalized value .up exponent ≤ 3 / 2 then
          exact
            { direction := .up
              exponent := exponent
              lower :=
                (by decide : (3 / 4 : Fraction.Rational) ≤ 1).trans baseLower
              upper := robust }
        else
          have baseLt : 3 / 2 < Basic.normalized value .up exponent :=
            lt_of_not_ge robust
          have relation : Basic.normalized value .up exponent =
              2 * Basic.normalized value .up previous := by
            rw [exponentIdentity]
            exact upSuccEqTwoUp value previous
          refine
            { direction := .up
              exponent := previous
              lower := ?_
              upper := previousUpper.le.trans (by decide) }
          rw [relation] at baseLt
          apply Arithmetic.le_of_mul_le_mul_right_direct
            (c := (2 : Fraction.Rational))
          · calc
              (3 / 4 : Fraction.Rational) * 2 = 3 / 2 := by decide
              _ ≤ 2 * Basic.normalized value .up previous := baseLt.le
              _ = Basic.normalized value .up previous * 2 :=
                Fraction.Field.mul_comm _ _
          · decide
  exact if oneLe : 1 ≤ value then normalizeHigh value
    positive oneLe
    else normalizeLow value positive (lt_of_not_ge
      oneLe)

end Normalization
end Purelib.Data.Rat.Dyadic

end
