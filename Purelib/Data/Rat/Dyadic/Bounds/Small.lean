module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.CrossMultiply
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.NatCast
import Purelib.Data.Rat.NatCast
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

section
@[expose] public section

/-!
# Generated sample certificates for the quartic A-backward connector

This module identifies the 64 canonical centred edges of the explicit
A-backward horizontal path with the independently generated rational root
and sample data.  The reversed stationary prefix is handled separately as a
zero-displacement path.
-/

namespace Purelib.Data.Rat.Dyadic.Bounds.Small

open Purelib.Data.Rat
/-- The canonical rational number two is positive. -/
theorem aBackwardTwoPositive : (0 : Fraction.Rational) < 2 :=
  Fraction.Cast.Order.natCast_pos_direct (n := 2) (by omega)

/-- The canonical rational number one half is positive. -/
theorem aBackwardOneHalfPositive : (0 : Fraction.Rational) < 1 / 2 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
      aBackwardTwoPositive

/-- The canonical rational number one quarter is positive. -/
theorem aBackwardOneFourthPositive : (0 : Fraction.Rational) < 1 / 4 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
      (Fraction.Cast.Order.natCast_pos_direct (n := 4) (by omega))
end Purelib.Data.Rat.Dyadic.Bounds.Small

end

section
@[expose] public section

/-!
# Generated sample certificates for the quartic B-backward connector

This module connects the 128 generated rational root and quotient samples to
the canonical centred edges already cached by the explicit B-backward bank.
The prepared-cell accessors keep these proofs from reconstructing the
dependent owner thread.
-/

namespace Purelib.Data.Rat.Dyadic.Bounds.Small

open Purelib.Data.Rat
/-- The canonical rational number one quarter is positive. -/
theorem bBackwardOneFourthPositive : (0 : Fraction.Rational) < 1 / 4 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
    (Fraction.Cast.Order.natCast_pos_direct (n := 4) (by omega))

/-- The canonical rational number one sixteenth is positive. -/
theorem bBackwardOneSixteenthPositive : (0 : Fraction.Rational) < 1 / 16 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
    (Fraction.Cast.Order.natCast_pos_direct (n := 16) (by omega))
end Purelib.Data.Rat.Dyadic.Bounds.Small

end

section
@[expose] public section

/-! # Generated sample certificates for the quartic B-forward connector -/

namespace Purelib.Data.Rat.Dyadic.Bounds.Small

open Purelib.Data.Rat
/-- The canonical rational number one quarter is positive. -/
theorem bForwardOneFourthPositive : (0 : Fraction.Rational) < 1 / 4 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
    (Fraction.Cast.Order.natCast_pos_direct (n := 4) (by omega))

/-- The canonical rational number one sixteenth is positive. -/
theorem bForwardOneSixteenthPositive : (0 : Fraction.Rational) < 1 / 16 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
    (Fraction.Cast.Order.natCast_pos_direct (n := 16) (by omega))
end Purelib.Data.Rat.Dyadic.Bounds.Small

end

section
@[expose] public section

/-!
# Generated sample certificates for the horizontal quartic connector

This module connects the untrusted generated rational root data to the exact
prepared edges cached by the A-forward construction.  The common helpers keep
the proof cost linear in the 64 nonstationary horizontal edges.
-/

namespace Purelib.Data.Rat.Dyadic.Bounds.Small

open Purelib.Data.Rat
/-- The canonical rational number thirteen thirty-seconds is positive. -/
theorem zero_lt_thirteenThirtySeconds :
    (0 : Fraction.Rational) < 13 / 32 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Order.NatCast.natCast_pos_direct 13 (by omega))
    (Fraction.Order.NatCast.natCast_pos_direct 32 (by omega))

/-- Thirteen thirty-seconds is at most thirty-one thirty-seconds. -/
theorem thirteenThirtySeconds_le_thirtyOneThirtySeconds :
    (13 / 32 : Fraction.Rational) <= 31 / 32 := by
  apply Fraction.Order.CrossMultiply.horizontalDivLeDivOfCrossMul
    (Fraction.Order.NatCast.natCast_pos_direct 32 (by omega))
    (Fraction.Order.NatCast.natCast_pos_direct 32 (by omega))
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Cast.Order.natCast_le_direct (by omega : 13 <= 31))
    ((fun n => Fraction.Cast.Order.natCast_le_direct (Nat.zero_le n)) 32)

/-- Thirteen thirty-seconds is at most eleven sixteenths. -/
theorem thirteenThirtySeconds_le_elevenSixteenths :
    (13 / 32 : Fraction.Rational) <= 11 / 16 := by
  apply Fraction.Order.CrossMultiply.horizontalDivLeDivOfCrossMul
    (Fraction.Order.NatCast.natCast_pos_direct 32 (by omega))
    (Fraction.Order.NatCast.natCast_pos_direct 16 (by omega))
  calc
    (13 : Fraction.Rational) * 16 = 208 := by ring1
    _ <= 352 := Fraction.Cast.Order.natCast_le_direct
      (m := 208) (n := 352) (by omega)
    _ = (11 : Fraction.Rational) * 32 := by ring1

/-- One eighth is at most the square of thirteen thirty-seconds. -/
theorem oneEighth_le_thirteenThirtySeconds_sq :
    (1 / 8 : Fraction.Rational) <= (13 / 32) ^ 2 := by
  have quotient : (1 / 8 : Fraction.Rational) <= 169 / 1024 := by
    apply Fraction.Order.CrossMultiply.horizontalDivLeDivOfCrossMul
      (Fraction.Order.NatCast.natCast_pos_direct 8 (by omega))
      (Fraction.Order.NatCast.natCast_pos_direct 1024 (by omega))
    calc
      (1 : Fraction.Rational) * 1024 = 1024 := by ring1
      _ <= 1352 := Fraction.Cast.Order.natCast_le_direct
        (m := 1024) (n := 1352) (by omega)
      _ = (169 : Fraction.Rational) * 8 := by ring1
  calc
    (1 / 8 : Fraction.Rational) <= 169 / 1024 := quotient
    _ = (13 / 32 : Fraction.Rational) ^ 2 := by
      rw [pow_two, Fraction.Field.div_mul_div_direct]
      rw [show (13 : Fraction.Rational) * 13 = 169 by ring1,
        show (32 : Fraction.Rational) * 32 = 1024 by ring1]

/-- Four times one eighth equals one half in the canonical rational carrier. -/
theorem fourTimesOneEighth_eq_oneHalf :
    (4 : Fraction.Rational) * (1 / 8) = 1 / 2 := by
  calc
    (4 : Fraction.Rational) * (1 / 8) = 4 / 8 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = 1 / 2 := by
      apply Fraction.Field.div_eq_div_of_cross_mul
        (Fraction.Order.NatCast.natCast_pos_direct 8 (by omega)).ne'
        (Fraction.Order.NatCast.natCast_pos_direct 2 (by omega)).ne'
      ring1

/-- One over 1048576 is at most one over 2048. -/
theorem horizontalFineResidual_le_coarse :
    (1 / 1048576 : Fraction.Rational) <= 1 / 2048 := by
  apply Fraction.Order.CrossMultiply.horizontalDivLeDivOfCrossMul
    (Fraction.Order.NatCast.natCast_pos_direct 1048576 (by omega))
    (Fraction.Order.NatCast.natCast_pos_direct 2048 (by omega))
  calc
    (1 : Fraction.Rational) * 2048 = 2048 := by ring1
    _ <= 1048576 := Fraction.Cast.Order.natCast_le_direct
      (m := 2048) (n := 1048576) (by omega)
    _ = (1 : Fraction.Rational) * 1048576 := by ring1

/-- The canonical rational number one half is positive. -/
theorem horizontalHalfPositive : (0 : Fraction.Rational) < 1 / 2 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Order.NatCast.natCast_pos_direct 1 (by omega))
    (Fraction.Order.NatCast.natCast_pos_direct 2 (by omega))

/-- One eighth is at most one half in the canonical rational carrier. -/
private theorem horizontalOneEighth_le_oneHalf :
    (1 / 8 : Fraction.Rational) <= 1 / 2 := by
  apply Fraction.Order.CrossMultiply.horizontalDivLeDivOfCrossMul
    (Fraction.Order.NatCast.natCast_pos_direct 8 (by omega))
    (Fraction.Order.NatCast.natCast_pos_direct 2 (by omega))
  calc
    (1 : Fraction.Rational) * 2 = 2 := by ring1
    _ <= 8 := Fraction.Cast.Order.natCast_le_direct
      (m := 2) (n := 8) (by omega)
    _ = (1 : Fraction.Rational) * 8 := by ring1

/-- The product of one eighth and one half is positive. -/
theorem horizontalLowerProductPositive :
    (0 : Fraction.Rational) < (1 / 8) * (1 / 2) :=
  Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.NatCast.natCast_pos_direct 1 (by omega))
      (Fraction.Order.NatCast.natCast_pos_direct 8 (by omega)))
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.NatCast.natCast_pos_direct 1 (by omega))
      (Fraction.Order.NatCast.natCast_pos_direct 2 (by omega)))

end Purelib.Data.Rat.Dyadic.Bounds.Small

end

section
@[expose] public section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

namespace Purelib.Data.Rat.Dyadic.Bounds.Small

open Purelib.Data.Rat
/-- One over 1024 is at most one in the canonical rational order. -/
theorem firstConnectorOneOver1024_le_one : (1 / 1024 : Fraction.Rational) <=
  1 := by
  have divOne : (1 : Fraction.Rational) / 1 = 1 := by
    rfl
  calc
    (1 / 1024 : Fraction.Rational) <= 1 / 1 := by
      apply Fraction.Compatibility.divLeDivOfCrossMul (Fraction.Order.NatCast.natCast_pos_direct 1024 (by omega))
        (Fraction.Order.NatCast.natCast_pos_direct 1 (by omega))
      calc
        (1 : Fraction.Rational) * ((1 : Nat) : Fraction.Rational) = ((1 : Nat) : Fraction.Rational) := by ring1
        _ <= ((1024 : Nat) : Fraction.Rational) := Fraction.Cast.Order.natCast_le_direct
          (by decide : 1 <= 1024)
        _ = 1 * ((1024 : Nat) : Fraction.Rational) := by ring1
    _ = 1 := divOne

/-- Four times the sum of two to the negative twelfth and one over 2048 is at most three over 1024. -/
theorem firstConnectorCandidateZeroTotalBudget :
    4 * ((1 : Fraction.Rational) / (2 ^ 12) + 1 / 2048) <= 3 / 1024 := by
  have powerTwelve : (2 : Fraction.Rational) ^ 12 = 4096 := by ring1
  have residualCommon : (1 / 2048 : Fraction.Rational) = 2 / 4096 := by
    apply Fraction.Compatibility.divEqOfNatDenominators (leftDenominator := 2048)
      (rightDenominator := 4096) (by omega) (by omega)
    ring1
  have resultCommon : (3 / 1024 : Fraction.Rational) = 12 / 4096 := by
    apply Fraction.Compatibility.divEqOfNatDenominators (leftDenominator := 1024)
      (rightDenominator := 4096) (by omega) (by omega)
    ring1
  rw [powerTwelve, residualCommon, resultCommon]
  apply le_of_eq
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- Two consecutive rational eighth-grid parameters have squared difference one over 64. -/
public theorem adjacentEighthParameters (value : Fraction.Rational) :
    (value / 8 - (value + 1) / 8) ^ 2 = (1 / 64 : Fraction.Rational) := by
  have difference : value / 8 - (value + 1) / 8 = (-1) / 8 := by
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [difference, pow_two, Fraction.Field.div_mul_div_direct]
  rw [show (-1 : Fraction.Rational) * (-1) = 1 by ring1,
    show (8 : Fraction.Rational) * 8 = 64 by ring1]

/-- The reciprocal of sixteen times eight is at most one. -/
public theorem oneOver128LeOne : (1 / (16 * 8) : Fraction.Rational) ≤ 1 :=
  by
  have denominatorPositive : (0 : Fraction.Rational) < 16 * 8 :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.NatCast.natCast_pos_direct 16 (by omega)) (Fraction.Order.NatCast.natCast_pos_direct 8 (by omega))
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := (16 : Fraction.Rational) * 8) _ denominatorPositive
  rw [Fraction.Field.div_mul_cancel_of_ne _ _
    denominatorPositive.ne']
  calc
    (1 : Fraction.Rational) = 0 + 1 := by ring1
    _ ≤ 127 + 1 :=
      Fraction.Order.Arithmetic.add_le_add_right_direct
        ((fun n => Fraction.Cast.Order.natCast_le_direct (Nat.zero_le n)) 127) 1
    _ = 1 * ((16 : Fraction.Rational) * 8) := by ring1

/-- A nonnegative rational at most three halves has one quarter of its square at most nine sixteenths. -/
public theorem quarterSquare_le_nineSixteenths (bound : Fraction.Rational)
    (nonnegative : 0 ≤ bound) (upper : bound ≤ 3 / 2) :
    bound ^ 2 / 4 ≤ (9 / 16 : Fraction.Rational) := by
  have squareLe : bound ^ 2 ≤ (3 / 2 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative upper 2
  calc
    bound ^ 2 / 4 ≤ (3 / 2 : Fraction.Rational) ^ 2 / 4 := by
      change bound ^ 2 * (4 : Fraction.Rational)⁻¹ ≤ (3 / 2 : Fraction.Rational) ^ 2 * (4 : Fraction.Rational)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        squareLe (Fraction.Order.Field.inv_pos_direct (by decide)).le
    _ = (9 / 16 : Fraction.Rational) := by with_unfolding_all decide

/-- A nonnegative rational at most thirteen eighths has one quarter of its square at most three halves. -/
public theorem quarterSquare_le_threeHalves_of_le_thirteenEighths
    (bound : Fraction.Rational) (nonnegative : 0 ≤ bound) (upper : bound ≤ 13 / 8) :
    bound ^ 2 / 4 ≤ (3 / 2 : Fraction.Rational) := by
  have squareLe : bound ^ 2 ≤ (13 / 8 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative upper 2
  calc
    bound ^ 2 / 4 ≤ (13 / 8 : Fraction.Rational) ^ 2 / 4 := by
      change bound ^ 2 * (4 : Fraction.Rational)⁻¹ ≤ (13 / 8 : Fraction.Rational) ^ 2 * (4 : Fraction.Rational)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        squareLe (Fraction.Order.Field.inv_pos_direct (by decide)).le
    _ ≤ (3 / 2 : Fraction.Rational) := by with_unfolding_all decide

/-- Forty over 64 equals five eighths in the canonical rational carrier. -/
public theorem fortyOver64EqFiveEighths : (40 / 64 : Fraction.Rational) = 5
  / 8 := by
  have sixtyFourNonzero : (64 : Fraction.Rational) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using (Fraction.Order.NatCast.natCast_pos_direct 64 (by omega)).ne'
  have eightNonzero : (8 : Fraction.Rational) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using (Fraction.Order.NatCast.natCast_pos_direct 8 (by omega)).ne'
  apply Fraction.Field.div_eq_div_of_cross_mul
    sixtyFourNonzero eightNonzero
  ring1

/-- Nine sixteenths is at most thirty-nine over 64. -/
public theorem nineSixteenthsLeThirtyNineSixtyFour :
    (9 / 16 : Fraction.Rational) ≤ 39 / 64 := by
  apply Fraction.Compatibility.divLeDivOfCrossMul (Fraction.Order.NatCast.natCast_pos_direct 16 (by omega))
    (Fraction.Order.NatCast.natCast_pos_direct 64 (by omega))
  calc
    (9 : Fraction.Rational) * 64 = 576 := by ring1
    _ ≤ 624 := Fraction.Cast.Order.natCast_le_direct (by decide)
    _ = 39 * 16 := by ring1

/-- A nonnegative rational at most two has one quarter of its square at most three halves. -/
public theorem quarterSquare_le_threeHalves_of_le_two
    (bound : Fraction.Rational) (nonnegative : 0 ≤ bound) (upper : bound ≤ 2) :
    bound ^ 2 / 4 ≤ (3 / 2 : Fraction.Rational) := by
  have squareLe : bound ^ 2 ≤ (2 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative upper 2
  calc
    bound ^ 2 / 4 ≤ (2 : Fraction.Rational) ^ 2 / 4 := by
      change bound ^ 2 * (4 : Fraction.Rational)⁻¹ ≤ (2 : Fraction.Rational) ^ 2 * (4 : Fraction.Rational)⁻¹
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        squareLe (Fraction.Order.Field.inv_pos_direct (by decide)).le
    _ ≤ (3 / 2 : Fraction.Rational) := by with_unfolding_all decide

end Purelib.Data.Rat.Dyadic.Bounds.Small

end
