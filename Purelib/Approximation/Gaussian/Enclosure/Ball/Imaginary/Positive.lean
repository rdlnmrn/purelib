module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Enclosure (Ball)

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Automatic discovery of the initial positive enclosure

A cached rational ball passes when its centre is above the real axis and its
squared radius is below the squared half-height. The soundness proof gives a
positive imaginary lower bound for every point in that ball. Failed tests
perform one canonical finite refinement; bounded runs retain their exact
state on exhaustion and never infer a negative positivity verdict.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive

/-- A sufficient, decidable rational test, with no square root calculation. -/
def PositiveTest (ball :
    Ball) : Prop
  :=
  0 < ball.center.im ∧ ball.radiusSq < (ball.center.im / 2) ^ 2

/-- Decide the positive-height enclosure test using exact rational comparisons. -/
instance instDecidablePositiveTest (ball :
  Ball) : Decidable
      (PositiveTest ball) :=
  inferInstanceAs (Decidable (0 < ball.center.im ∧ ball.radiusSq < (ball.center.im / 2) ^ 2))

/-- A passing positive-height test gives a strictly positive half-height. -/
theorem half_positive {ball :
    Ball}
  (test : PositiveTest ball) :
    0 < ball.center.im / 2 :=
  Fraction.Order.Field.div_pos_direct test.1 (by decide)

/-- Every rational reading in a passing ball has at least half the positive centre height. This is whole-ball evidence,
not just a centre observation. -/
theorem positiveTest_sound {ball :
  Ball} (test : PositiveTest
      ball)
    {value : Data.Gaussian.Basic.Canonical} (inside : ball.Contains value) :
    ball.center.im / 2 ≤ value.im := by
  change (value.re - ball.center.re) ^ 2 + (value.im - ball.center.im) ^ 2 ≤
    ball.radiusSq at inside
  have squareLe : (value.im - ball.center.im) ^ 2 ≤ ball.radiusSq :=
    (le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct (value.re - ball.center.re))).trans inside
  have lower := Fraction.Order.Arithmetic.neg_le_of_sq_le_sq_direct
    (half_positive test).le (squareLe.trans_lt test.2).le
  calc
    ball.center.im / 2 = -(ball.center.im / 2) + (ball.center.im / 2) * 2 := by ring1
    _ = -(ball.center.im / 2) + ball.center.im := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide : (2 : Fraction.Rational) ≠ 0)]
    _ ≤ (value.im - ball.center.im) + ball.center.im :=
      Fraction.Order.Arithmetic.add_le_add_right_direct lower ball.center.im
    _ = value.im := by ring1
end Purelib.Approximation.Gaussian.Enclosure.Ball.Imaginary.Positive

end
