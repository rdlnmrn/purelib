module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Nat.BinaryNormalization
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Gaussian.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

section
public section

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace Purelib.Approximation.Rational.Geometric.Upscale

open Purelib.Algebra

open Purelib

open Purelib.Data.Nat

open Purelib.Data.Rat

open Purelib.Data.Rat.Rounding

/-! ## Initial low-chart scaling -/

/-- Explicit finite exponent which scales any positive rational lower norm strictly above one. -/
@[expose] def upscaleExponent (lowerSq : Fraction.Rational) : Nat :=
  Floor.ceilNat (1 / lowerSq) + 1

/-- The computed exponent scales a positive lower quadrance strictly above one. -/
theorem upscaleExponent_lower {lowerSq : Fraction.Rational}
    (positive : 0 < lowerSq) :
    1 < (2 : Fraction.Rational) ^ upscaleExponent lowerSq * lowerSq := by
  let inverse : Fraction.Rational := 1 / lowerSq
  let ceiling := Floor.ceilNat inverse
  have inverseNonnegative : 0 ≤ inverse :=
    (Fraction.Order.Field.div_pos_direct (by decide) positive).le
  have inverseLe : inverse ≤ (ceiling : Nat) := by
    exact Floor.le_natCast_ceilNat_of_nonneg
      inverseNonnegative
  have oneLe : 1 ≤ (ceiling : Fraction.Rational) * lowerSq := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        inverseLe positive.le
    calc
      1 = inverse * lowerSq := by
        dsimp only [inverse]
        exact (Fraction.Field.div_mul_cancel_of_ne 1 lowerSq
          positive.ne').symm
      _ ≤ (ceiling : Fraction.Rational) * lowerSq := scaled
  have ceilingStrict : (ceiling : Fraction.Rational) * lowerSq <
      ((ceiling + 1 : Nat) : Fraction.Rational) * lowerSq := by
    apply Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      _ positive
    exact Fraction.Cast.Order.natCast_lt_direct (Nat.lt_succ_self _)
  have successorLower : 1 <
      ((ceiling + 1 : Nat) : Fraction.Rational) * lowerSq :=
    oneLe.trans_lt ceilingStrict
  have powerBoundNat : ceiling + 1 ≤ 2 ^ (ceiling + 1) := by
    exact (BinaryNormalization.succ_le_two_pow (ceiling + 1)).trans'
      (Nat.le_succ (ceiling + 1))
  have powerBound : ((ceiling + 1 : Nat) : Fraction.Rational) ≤
      (2 : Fraction.Rational) ^ (ceiling + 1) := by
    have castBound := Fraction.Cast.Order.natCast_le_direct powerBoundNat
    simpa only [Purelib.Algebra.NatCast.pow, Nat.cast_ofNat] using castBound
  have scaledPower :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct powerBound
      positive.le
  dsimp only [upscaleExponent, ceiling]
  exact successorLower.trans_le scaledPower

/-- Adding any prior exponent preserves the strict lower bound above one. -/
theorem upscaledPrefix_lower
    (priorCount : Nat) {lowerSq : Fraction.Rational} (positive : 0 < lowerSq) :
    1 < (2 : Fraction.Rational) ^ (priorCount + upscaleExponent lowerSq) *
      lowerSq := by
  have baseLower := upscaleExponent_lower positive
  have powerOne : (1 : Fraction.Rational) ≤ (2 : Fraction.Rational) ^ priorCount := by
    have monotone := Fraction.Order.Arithmetic.pow_le_pow_direct
      (by decide : (0 : Fraction.Rational) ≤ 1)
      (by decide : (1 : Fraction.Rational) ≤ 2) priorCount
    simpa only [one_pow] using monotone
  calc
    1 < (2 : Fraction.Rational) ^ upscaleExponent lowerSq * lowerSq :=
      baseLower
    _ ≤ (2 : Fraction.Rational) ^ priorCount *
        ((2 : Fraction.Rational) ^ upscaleExponent lowerSq * lowerSq) := by
      calc
        (2 : Fraction.Rational) ^ upscaleExponent lowerSq * lowerSq =
            1 * ((2 : Fraction.Rational) ^ upscaleExponent lowerSq * lowerSq)
              :=
          (_root_.one_mul _).symm
        _ ≤ (2 : Fraction.Rational) ^ priorCount *
            ((2 : Fraction.Rational) ^ upscaleExponent lowerSq * lowerSq) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            powerOne
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)
              positive.le)
    _ = (2 : Fraction.Rational) ^ (priorCount + upscaleExponent lowerSq) *
      lowerSq := by
      rw [pow_add]
      ring1
end Purelib.Approximation.Rational.Geometric.Upscale

end
