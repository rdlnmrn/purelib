module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
public import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
-- Initial.Budget deliberately retains this owner through its public proof API.
import Purelib.Data.Rat.Bounds.Tenth
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Low.Budget

open Purelib.Data.Rat in
/-- The exact rational low-center slack (1/25)/8. -/
public def lowCenterSlack : Fraction.Rational := (1 / 25) / 8

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- The retained low-center slack is strictly positive. -/
private theorem lowCenterSlack_pos : 0 <
  Emission.Low.Budget.lowCenterSlack := by
  unfold Emission.Low.Budget.lowCenterSlack
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct (by decide) (by decide))
    (by decide)

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Twice the uniform sector radius-squared budget is strictly below the retained low-center slack. -/
public theorem two_uniform_lt_lowCenterSlack :
    2 * Enclosure.Sector.Budget.uniformRadiusSq < Emission.Low.Budget.lowCenterSlack := by
  have divided :
      Enclosure.Sector.Budget.allowance / 8 <
        (1 / 25 : Fraction.Rational) / 8 := by
    apply (Fraction.Order.Field.div_lt_iff_pos
      (by decide : (0 : Fraction.Rational) < 8)).2
    calc
      Enclosure.Sector.Budget.allowance < (1 / 25 : Fraction.Rational) :=
        Emission.Initial.Budget.allowance_lt_one_twenty_fifth
      _ = ((1 / 25 : Fraction.Rational) / 8) * 8 :=
        (Fraction.Field.div_mul_cancel_of_ne _ 8 (by decide)).symm
  have identity :
      2 * Enclosure.Sector.Budget.uniformRadiusSq =
        Enclosure.Sector.Budget.allowance / 8 := by
    unfold Enclosure.Sector.Budget.uniformRadiusSq
    have twoDivOne : (2 / 1 : Fraction.Rational) = 2 := by
      calc
        (2 / 1 : Fraction.Rational) = (2 / 1) * 1 :=
          (Fraction.Field.mul_one_direct _).symm
        _ = 2 :=
          Fraction.Field.div_mul_cancel_of_ne 2 1 (by decide)
    calc
      2 * (Enclosure.Sector.Budget.allowance / 16) =
          (Enclosure.Sector.Budget.allowance / 16) * (2 / 1) := by
        rw [twoDivOne, Fraction.Field.mul_comm]
      _ = (Enclosure.Sector.Budget.allowance * 2) / (16 * 1) :=
        Fraction.Field.div_mul_div_direct _ _ _ _
      _ = (2 * Enclosure.Sector.Budget.allowance) / (2 * 8) := by
        apply congrArg₂ (fun numerator denominator : Fraction.Rational =>
          numerator / denominator)
        · exact Fraction.Field.mul_comm _ _
        · decide
      _ = Enclosure.Sector.Budget.allowance / 8 :=
        Fraction.Field.mul_div_mul_left_direct 2 _ _ (by decide)
  exact identity.trans_lt divided

open Purelib.Data.Rat in
/-- The exact low-center precision weight (10 times 10) times 10. -/
public def lowCenterWeight : Fraction.Rational := (10 * 10) * 10

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- The retained low-center precision weight is strictly positive. -/
public theorem lowCenterWeight_pos : 0 <
  Emission.Low.Budget.lowCenterWeight := by
  unfold Emission.Low.Budget.lowCenterWeight
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct Bounds.Tenth.ten_pos Bounds.Tenth.ten_pos) Bounds.Tenth.ten_pos

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- The retained low-center weight times the initial radius-squared budget equals the uniform sector budget. -/
public theorem lowCenterWeight_mul_initial :
    Emission.Low.Budget.lowCenterWeight * Emission.Initial.Budget.initialRadiusSq =
      Enclosure.Sector.Budget.uniformRadiusSq := by
  let uniform := Enclosure.Sector.Budget.uniformRadiusSq
  have tenNonzero : (10 : Fraction.Rational) ≠ 0 := Bounds.Tenth.ten_pos.ne'
  calc
    Emission.Low.Budget.lowCenterWeight * Emission.Initial.Budget.initialRadiusSq =
        (((uniform / 10) / 10) / 10) * ((10 * 10) * 10) := by
      unfold Emission.Low.Budget.lowCenterWeight Emission.Initial.Budget.initialRadiusSq
      ring1
    _ = ((((uniform / 10) / 10) / 10) * 10) * 10 * 10 := by
      ring1
    _ = ((uniform / 10) / 10) * 10 * 10 := by
      have cancellation : (((uniform / 10) / 10) / 10) * 10 =
          (uniform / 10) / 10 :=
        Fraction.Field.div_mul_cancel_of_ne _ 10 tenNonzero
      rw [cancellation]
    _ = (uniform / 10) * 10 := by
      have cancellation : ((uniform / 10) / 10) * 10 = uniform / 10 :=
        Fraction.Field.div_mul_cancel_of_ne _ 10 tenNonzero
      rw [cancellation]
    _ = uniform :=
      Fraction.Field.div_mul_cancel_of_ne _ 10 tenNonzero

open Purelib.Data.CCL.Transducer in
/-- The retained low-center slack times its exact weight equals five. -/
public theorem lowCenterSlack_mul_weight :
    Emission.Low.Budget.lowCenterSlack * Emission.Low.Budget.lowCenterWeight = 5 := by
  unfold Emission.Low.Budget.lowCenterSlack Emission.Low.Budget.lowCenterWeight
  decide

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- The low-state bound 43/20 plus twice the retained center slack is strictly below 13/6. -/
public theorem lowCenter_budget :
    (43 / 20 : Fraction.Rational) + Emission.Low.Budget.lowCenterSlack + Emission.Low.Budget.lowCenterSlack < 13 / 6 :=
      by
  have eightNonzero : (8 : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 8) (by decide)).ne'
  have twentyFiveNonzero : (25 : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 25) (by decide)).ne'
  have twoHundredNonzero : (200 : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 200) (by decide)).ne'
  have slackValue : Emission.Low.Budget.lowCenterSlack = (1 / 200 : Fraction.Rational) := by
    unfold Emission.Low.Budget.lowCenterSlack
    apply Fraction.Field.div_eq_div_of_cross_mul
      eightNonzero twoHundredNonzero
    calc
      (1 / 25 : Fraction.Rational) * 200 = ((1 / 25) * 25) * 8 := by ring1
      _ = 1 * 8 := by
        rw [Fraction.Field.div_mul_cancel_of_ne
          1 25 twentyFiveNonzero]
      _ = (1 : Fraction.Rational) * 8 := rfl
  rw [slackValue]
  have twentyNonzero : (20 : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 20) (by decide)).ne'
  have sixNonzero : (6 : Fraction.Rational) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 6) (by decide)).ne'
  have firstScaled : (43 / 20 : Fraction.Rational) * 600 = 1290 := by
    calc
      (43 / 20 : Fraction.Rational) * 600 = ((43 / 20) * 20) * 30 := by ring1
      _ = 43 * 30 := by
        rw [Fraction.Field.div_mul_cancel_of_ne
          43 20 twentyNonzero]
      _ = 1290 := by ring1
  have slackScaled : (1 / 200 : Fraction.Rational) * 600 = 3 := by
    calc
      (1 / 200 : Fraction.Rational) * 600 = ((1 / 200) * 200) * 3 := by ring1
      _ = 1 * 3 := by
        rw [Fraction.Field.div_mul_cancel_of_ne
          1 200 twoHundredNonzero]
      _ = 3 := Fraction.Field.one_mul _
  have upperScaled : (13 / 6 : Fraction.Rational) * 600 = 1300 := by
    calc
      (13 / 6 : Fraction.Rational) * 600 = ((13 / 6) * 6) * 100 := by ring1
      _ = 13 * 100 := by
        rw [Fraction.Field.div_mul_cancel_of_ne 13 6 sixNonzero]
      _ = 1300 := by ring1
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := 600)
  · calc
      ((43 / 20 : Fraction.Rational) + 1 / 200 + 1 / 200) * 600 =
          (43 / 20) * 600 + (1 / 200) * 600 + (1 / 200) * 600 := by ring1
      _ = 1290 + 3 + 3 := by rw [firstScaled, slackScaled]
      _ = 1296 := by ring1
      _ < 1300 := Fraction.Cast.Order.natCast_lt_direct (by decide)
      _ = (13 / 6 : Fraction.Rational) * 600 := upperScaled.symm
  · exact Fraction.Cast.Order.natCast_pos_direct
      (n := 600) (by decide)

open Purelib.Data.CCL.Transducer in
/-- Ten times the retained low-center slack equals one twentieth. -/
private theorem lowCenterSlack_mul_ten :
  Emission.Low.Budget.lowCenterSlack * 10 = 1 / 20 := by
  unfold Emission.Low.Budget.lowCenterSlack
  decide

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- One tenth of the fixed sector allowance is strictly below the retained low-center slack. -/
public theorem allowance_tenth_lt_lowCenterSlack :
    Enclosure.Sector.Budget.allowance / 10 < Emission.Low.Budget.lowCenterSlack := by
  apply (Fraction.Order.Field.div_lt_iff_pos Bounds.Tenth.ten_pos).2
  rw [Emission.Low.Budget.lowCenterSlack_mul_ten]
  exact Emission.Initial.Budget.allowance_lt_one_twenty_fifth.trans (by decide)

section
open Purelib.Data.Rat
/-- The exact rational low-unary gap (1/15)/8. -/
private def lowUnaryGap : Fraction.Rational := (1 / 15) / 8

/-- One twenty-fifth is strictly below one fifteenth. -/
private theorem oneTwentyFifth_lt_oneFifteenth :
    (1 / 25 : Fraction.Rational) < 1 / 15 := by
  have fifteenthPositive : (0 : Fraction.Rational) < 1 / 15 :=
    Fraction.Order.Field.div_pos_direct (by decide) (by decide)
  apply (Fraction.Order.Field.div_lt_iff_pos
    (by decide : (0 : Fraction.Rational) < 25)).2
  calc
    1 = (1 / 15 : Fraction.Rational) * 15 :=
      (Fraction.Field.div_mul_cancel_of_ne 1 15 (by decide)).symm
    _ < (1 / 15 : Fraction.Rational) * 25 :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        fifteenthPositive (by decide)

end

open Purelib.Data.CCL.Transducer
open Purelib.Data.Rat
/-- The retained low-center slack is strictly below the retained low-unary gap. -/
private theorem lowCenterSlack_lt_lowUnaryGap :
    Emission.Low.Budget.lowCenterSlack < Emission.Low.Budget.lowUnaryGap := by
  unfold Emission.Low.Budget.lowCenterSlack Emission.Low.Budget.lowUnaryGap
  apply (Fraction.Order.Field.div_lt_iff_pos
    (by decide : (0 : Fraction.Rational) < 8)).2
  calc
    (1 / 25 : Fraction.Rational) < 1 / 15 :=
      Emission.Low.Budget.oneTwentyFifth_lt_oneFifteenth
    _ = ((1 / 15 : Fraction.Rational) / 8) * 8 :=
      (Fraction.Field.div_mul_cancel_of_ne _ 8 (by decide)).symm

/-- The low-unary gap plus sixteen fifteenths equals forty-three fortieths. -/
private theorem lowUnaryGap_identity :
    Emission.Low.Budget.lowUnaryGap + (16 / 15 : Fraction.Rational) * 1 = 43 / 40 := by
  unfold Emission.Low.Budget.lowUnaryGap
  decide +kernel

/-- The retained low-center slack plus sixteen fifteenths is strictly below forty-three fortieths. -/
public theorem lowUnary_budget :
    Emission.Low.Budget.lowCenterSlack + (16 / 15 : Fraction.Rational) * 1 < 43 / 40 := by
  calc
    Emission.Low.Budget.lowCenterSlack + (16 / 15 : Fraction.Rational) * 1 <
        Emission.Low.Budget.lowUnaryGap + (16 / 15) * 1 :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct
        Emission.Low.Budget.lowCenterSlack_lt_lowUnaryGap _
    _ = 43 / 40 := Emission.Low.Budget.lowUnaryGap_identity

end Purelib.Data.CCL.Transducer.Emission.Low.Budget

end
