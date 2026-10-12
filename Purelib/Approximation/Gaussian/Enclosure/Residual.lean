module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite residual-small-or-apart decisions

After a redundant sector is emitted, an arithmetic result may equal the
sector representative without that equality being decidable from opaque
input names.  The controller therefore never asks for equality.  At a fixed
positive residual threshold, a sufficiently fine rational ball either proves
that every realization is small enough to justify unary padding, or supplies
a positive norm lower bound making affine inversion sound.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Residual

/-- Finite upper-bound certificate for every realization of a ball. -/
def SmallBall (ball : Approximation.Gaussian.Enclosure.Ball)
    (target :
  Fraction.Rational) : Prop :=
  2 * (ball.radiusSq + Data.Gaussian.Norm.Basic.normSq ball.center) < target

/-- Decide the sufficient small-ball test by exact rational comparison. -/
instance smallBallDecidable (ball :
    Approximation.Gaussian.Enclosure.Ball) (target :
  Fraction.Rational) :
    Decidable (SmallBall ball target) := by
  unfold SmallBall
  infer_instance

/-- Every reading in a ball passing the small-ball test has squared norm below the requested target. -/
theorem normSq_lt_of_contains {ball :
    Approximation.Gaussian.Enclosure.Ball} {target
  : Fraction.Rational}
    (small : SmallBall ball target) {value : Data.Gaussian.Basic.Canonical}
    (inside : ball.Contains value) : Data.Gaussian.Norm.Basic.normSq value < target := by
  have decomposition :
      value = (value - ball.center) + ball.center := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  rw [decomposition]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two (value - ball.center) ball.center).trans_lt
    (lt_of_le_of_lt
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add inside le_rfl) (by decide)) small)

/-- A centre separated from its own squared error yields an explicit lower norm for every realization. -/
def apartOfCenter (ball :
    Approximation.Gaussian.Enclosure.Ball)
    (separated : 2 * ball.radiusSq < Data.Gaussian.Norm.Basic.normSq ball.center) :
    Ball.Apart ball := by
  let lowerSq := Data.Gaussian.Norm.Basic.normSq ball.center / 2 - ball.radiusSq
  have lowerPositive : 0 < lowerSq := by
    apply Fraction.Order.Arithmetic.sub_pos_direct
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := (2 : Fraction.Rational)) _ (by decide)
    calc
      ball.radiusSq * 2 = 2 * ball.radiusSq :=
        Fraction.Field.mul_comm _ _
      _ < Data.Gaussian.Norm.Basic.normSq ball.center := separated
      _ = (Data.Gaussian.Norm.Basic.normSq ball.center / 2) * 2 :=
        (Fraction.Field.div_mul_cancel_of_ne
          (Data.Gaussian.Norm.Basic.normSq ball.center) 2 (by decide)).symm
  exact
    { lowerSq := lowerSq
      positive := lowerPositive
      lower := by
        intro value inside
        have errorNorm : Data.Gaussian.Norm.Basic.normSq (ball.center - value) ≤ ball.radiusSq := by
          have negDifference :
              ball.center - value = -(value - ball.center) := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
          rw [negDifference, Data.Gaussian.Norm.Basic.normSq_neg]
          exact inside
        have decomposition :
            ball.center = (ball.center - value) + value := by
          apply Data.Gaussian.Basic.ext <;>
            simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
              Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im] <;> ring1
        have centerUpper : Data.Gaussian.Norm.Basic.normSq ball.center ≤
            2 * (ball.radiusSq + Data.Gaussian.Norm.Basic.normSq value) := by
          rw [decomposition]
          exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two (ball.center - value) value).trans
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add errorNorm le_rfl) (by decide))
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
          (c := (2 : Fraction.Rational)) _ (by decide)
        calc
          lowerSq * 2 =
              (Data.Gaussian.Norm.Basic.normSq ball.center / 2) * 2 - ball.radiusSq * 2 := by
            dsimp only [lowerSq]
            ring1
          _ = Data.Gaussian.Norm.Basic.normSq ball.center - 2 * ball.radiusSq := by
            have cancelled :
                (Data.Gaussian.Norm.Basic.normSq ball.center / 2) * 2 =
                  Data.Gaussian.Norm.Basic.normSq ball.center :=
              Fraction.Field.div_mul_cancel_of_ne
                (Data.Gaussian.Norm.Basic.normSq ball.center) 2 (by decide)
            calc
              (Data.Gaussian.Norm.Basic.normSq ball.center / 2) * 2 - ball.radiusSq * 2 =
                  Data.Gaussian.Norm.Basic.normSq ball.center - ball.radiusSq * 2 :=
                congrArg (fun coordinate =>
                  coordinate - ball.radiusSq * 2) cancelled
              _ = Data.Gaussian.Norm.Basic.normSq ball.center - 2 * ball.radiusSq := by ring1
          _ ≤ 2 * Data.Gaussian.Norm.Basic.normSq value := by
            apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
              (c := 2 * ball.radiusSq)
            calc
              Data.Gaussian.Norm.Basic.normSq ball.center - 2 * ball.radiusSq +
                  2 * ball.radiusSq = Data.Gaussian.Norm.Basic.normSq ball.center := by ring1
              _ ≤ 2 * (ball.radiusSq + Data.Gaussian.Norm.Basic.normSq value) := centerUpper
              _ = 2 * Data.Gaussian.Norm.Basic.normSq value + 2 * ball.radiusSq := by ring1
          _ = Data.Gaussian.Norm.Basic.normSq value * 2 :=
            Fraction.Field.mul_comm _ _ }

set_option genInjectivity false in
/-- The two finite residual outcomes. -/
inductive Decision (ball :
    Approximation.Gaussian.Enclosure.Ball) (target :
  Fraction.Rational) where
  /-- A certificate that the ball passes the finite upper-bound test for the original target. -/ | small (certificate :
    SmallBall ball target)
  /-- An explicit positive lower quadrance valid for every reading admitted by the original ball. -/ | apart
    (certificate : Ball.Apart ball)

constructive_injectivity Decision

/-- Decide a sufficiently fine residual ball as small or positively apart.

A squared radius below one sixth of the positive target suffices; the outcomes retain either the finite small-ball test
or a whole-ball lower-quadrance certificate. -/
def decide (ball : Approximation.Gaussian.Enclosure.Ball)
    (target :
  Fraction.Rational) (_targetPositive : 0 < target)
    (fine : ball.radiusSq < target / 6) : Decision ball target := by
  by_cases small : SmallBall ball target
  · exact .small small
  · apply Decision.apart
    apply apartOfCenter
    by_contra notSeparated
    have centerUpper : Data.Gaussian.Norm.Basic.normSq ball.center ≤ 2 * ball.radiusSq :=
      le_of_not_gt notSeparated
    have certificateUpper :
        2 * (ball.radiusSq + Data.Gaussian.Norm.Basic.normSq ball.center) ≤
          6 * ball.radiusSq := by
      calc
        2 * (ball.radiusSq + Data.Gaussian.Norm.Basic.normSq ball.center) ≤
            2 * (ball.radiusSq + 2 * ball.radiusSq) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add le_rfl centerUpper) (by decide)
        _ = 6 * ball.radiusSq := by ring1
    have sixRadiusLt : 6 * ball.radiusSq < target := by
      have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide : (0 : Fraction.Rational) < 6) fine
      calc
        6 * ball.radiusSq < 6 * (target / 6) := scaled
        _ = target := by
          calc
            6 * (target / 6) = (target / 6) * 6 :=
              Fraction.Field.mul_comm _ _
            _ = target :=
              Fraction.Field.div_mul_cancel_of_ne target 6
                (by decide)
    have wouldBeSmall : SmallBall ball target :=
      certificateUpper.trans_lt sixRadiusLt
    exact small wouldBeSmall
end Purelib.Approximation.Gaussian.Enclosure.Residual

end
