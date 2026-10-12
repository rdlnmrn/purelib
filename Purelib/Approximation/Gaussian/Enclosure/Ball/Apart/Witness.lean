module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs

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

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.Apart.Witness

open Purelib
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Data.Rat

/-- A possible point with norm at least `lowerSq`, together with radius below `lowerSq/12`, forces the entire displayed
ball to stay at least `lowerSq/8` away from zero. -/
@[expose] public def apartBallOfPossibleLower (ball : Ball) (lowerSq : Fraction.Rational)
    (lowerPositive : 0 < lowerSq) (witness : Data.Gaussian.Basic.Canonical)
    (inside : ball.Contains witness) (witnessLower : lowerSq ≤ Data.Gaussian.Norm.Basic.normSq witness)
    (fine : ball.radiusSq < lowerSq / 12) :
    Ball.Apart ball := by
  let centerNorm := Data.Gaussian.Norm.Basic.normSq ball.center
  have witnessDecomposition :
      witness = (witness - ball.center) + ball.center := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
        Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im] <;> ring1
  have witnessUpper : Data.Gaussian.Norm.Basic.normSq witness ≤
      2 * (ball.radiusSq + centerNorm) := by
    rw [witnessDecomposition]
    exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two (witness - ball.center) ball.center).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add inside le_rfl) (by decide))
  have centerLower : lowerSq / 2 - ball.radiusSq ≤ centerNorm := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := (2 : Fraction.Rational)) _ (by decide)
    apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
      (c := 2 * ball.radiusSq)
    calc
      (lowerSq / 2 - ball.radiusSq) * 2 +
          2 * ball.radiusSq = lowerSq := by
        rw [show (lowerSq / 2 - ball.radiusSq) * 2 =
            (lowerSq / 2) * 2 - ball.radiusSq * 2 by ring1,
          Purelib.Data.Rat.Bounds.Quarter.half_mul_two]
        ring1
      _ ≤ Data.Gaussian.Norm.Basic.normSq witness := witnessLower
      _ ≤ 2 * (ball.radiusSq + centerNorm) := witnessUpper
      _ = centerNorm * 2 + 2 * ball.radiusSq := by ring1
  have twelveRadiusLt : ball.radiusSq * 12 < lowerSq :=
    (Fraction.Order.Field.lt_div_iff_pos
      (by decide : (0 : Fraction.Rational) < 12)).1 fine
  have sixRadiusLt : ball.radiusSq * 6 < lowerSq := by
    have radiusNonnegative := ball.radiusSq_nonneg
    have sixLeTwelve : ball.radiusSq * 6 ≤ ball.radiusSq * 12 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (by decide) radiusNonnegative
    exact sixLeTwelve.trans_lt twelveRadiusLt
  have separated : 2 * ball.radiusSq < centerNorm := by
    have beforeCenter :
        2 * ball.radiusSq < lowerSq / 2 - ball.radiusSq := by
      apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
        (c := ball.radiusSq)
      calc
        2 * ball.radiusSq + ball.radiusSq = 3 * ball.radiusSq := by ring1
        _ < lowerSq / 2 := by
          apply (Fraction.Order.Field.lt_div_iff_pos
            (by decide : (0 : Fraction.Rational) < 2)).2
          calc
            (3 * ball.radiusSq) * 2 = ball.radiusSq * 6 := by ring1
            _ < lowerSq := sixRadiusLt
        _ = (lowerSq / 2 - ball.radiusSq) + ball.radiusSq := by ring1
    exact beforeCenter.trans_le centerLower
  let raw := Residual.apartOfCenter ball separated
  have fixedLower : lowerSq / 8 ≤ raw.lowerSq := by
    dsimp only [raw, Residual.apartOfCenter]
    have twelveRadiusLe : ball.radiusSq * 12 ≤ lowerSq :=
      twelveRadiusLt.le
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := (8 : Fraction.Rational)) _ (by decide)
    calc
      (lowerSq / 8) * 8 = lowerSq :=
        Fraction.Field.div_mul_cancel_of_ne
          lowerSq 8 (by decide)
      _ ≤ 2 * lowerSq - ball.radiusSq * 12 := by
        apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
          (c := ball.radiusSq * 12)
        calc
          lowerSq + ball.radiusSq * 12 =
              ball.radiusSq * 12 + lowerSq := _root_.add_comm _ _
          _ ≤ lowerSq + lowerSq :=
            Fraction.Order.Arithmetic.add_le_add_right_direct
              twelveRadiusLe lowerSq
          _ = (2 * lowerSq - ball.radiusSq * 12) +
              ball.radiusSq * 12 := by ring1
      _ = (lowerSq / 2 - ball.radiusSq) * 4 -
          ball.radiusSq * 8 := by
        rw [show (lowerSq / 2 - ball.radiusSq) * 4 =
            ((lowerSq / 2) * 2) * 2 - ball.radiusSq * 4 by ring1,
          Purelib.Data.Rat.Bounds.Quarter.half_mul_two]
        ring1
      _ ≤ centerNorm * 4 - ball.radiusSq * 8 := by
        have scaledCenter :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            centerLower (by decide : (0 : Fraction.Rational) ≤ 4)
        calc
          (lowerSq / 2 - ball.radiusSq) * 4 - ball.radiusSq * 8 =
              (lowerSq / 2 - ball.radiusSq) * 4 +
                -(ball.radiusSq * 8) := _root_.sub_eq_add_neg _ _
          _ ≤ centerNorm * 4 + -(ball.radiusSq * 8) :=
            Fraction.Order.Arithmetic.add_le_add_right_direct
              scaledCenter (-(ball.radiusSq * 8))
          _ = centerNorm * 4 - ball.radiusSq * 8 :=
            (_root_.sub_eq_add_neg _ _).symm
      _ = (centerNorm / 2 - ball.radiusSq) * 8 := by
        rw [show (centerNorm / 2 - ball.radiusSq) * 8 =
            ((centerNorm / 2) * 2) * 4 - ball.radiusSq * 8 by ring1,
          Purelib.Data.Rat.Bounds.Quarter.half_mul_two]
  exact
    { lowerSq := lowerSq / 8
      positive := Fraction.Order.Field.div_pos_direct lowerPositive
        (by decide)
      lower := fun insideValue => fixedLower.trans (raw.lower insideValue) }

end Purelib.Approximation.Gaussian.Enclosure.Ball.Apart.Witness

end
