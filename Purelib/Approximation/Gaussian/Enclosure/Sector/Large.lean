module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat

section
@[expose] public section

/-!
# A finite redundant output decision for CCL arithmetic

The canonical comparison at squared norm `2` is not stable under finite
enclosures.  This module gives the arithmetic transducer a separate finite
decision.  A sufficiently accurate ball whose centre has squared norm at
least one is either wholly in the next-unary region or wholly safe for one
of the eight sector representatives.

The constants are intentionally rational and square-root-free.  Safe-sector
coverage extends through squared norm `13/6`; the unary test starts below
that bound, at `32/15` plus the displayed error.  Their positive overlap is
the finite reason the controller cannot stall at squared norm `2`.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Sector.Large

/-- A finite sufficient test that the whole ball lies strictly above the canonical radial boundary. -/
def UnaryBall (ball :
    Approximation.Gaussian.Enclosure.Ball) : Prop :=
  (16 / 15) * 2 + 16 * ball.radiusSq < Data.Gaussian.Norm.Basic.normSq ball.center

/-- Decide the sufficient unary-ball test using exact rational comparison. -/
instance unaryBallDecidable (ball :
    Approximation.Gaussian.Enclosure.Ball) :
  Decidable (UnaryBall ball) := by
  unfold UnaryBall
  infer_instance

/-- Every reading in a ball passing the unary test has squared norm strictly greater than two. -/
theorem normSq_gt_two_of_contains {ball :
    Approximation.Gaussian.Enclosure.Ball}
  {value : Data.Gaussian.Basic.Canonical}
    (certificate : UnaryBall ball) (inside : ball.Contains value) :
    2 < Data.Gaussian.Norm.Basic.normSq value := by
  have centerDifference :
      ball.center = (ball.center - value) + value := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  have errorNorm : Data.Gaussian.Norm.Basic.normSq (ball.center - value) ≤ ball.radiusSq := by
    have negDifference : ball.center - value = -(value - ball.center) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im] <;> ring1
    rw [negDifference, Data.Gaussian.Norm.Basic.normSq_neg]
    exact inside
  have centerUpper : Data.Gaussian.Norm.Basic.normSq ball.center ≤
      16 * ball.radiusSq + (16 / 15) * Data.Gaussian.Norm.Basic.normSq value := by
    rw [centerDifference]
    exact (Weighted.normSq_add_le_weighted (ball.center - value) value).trans
      (add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          errorNorm (by decide)) le_rfl)
  have scaledStrict :
      (16 / 15) * 2 < (16 / 15) * Data.Gaussian.Norm.Basic.normSq value := by
    apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
      (c := 16 * ball.radiusSq)
    calc
      (16 / 15) * 2 + 16 * ball.radiusSq < Data.Gaussian.Norm.Basic.normSq ball.center :=
        certificate
      _ ≤ 16 * ball.radiusSq + (16 / 15) * Data.Gaussian.Norm.Basic.normSq value := centerUpper
      _ = (16 / 15) * Data.Gaussian.Norm.Basic.normSq value + 16 * ball.radiusSq := by ring1
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := (16 / 15 : Fraction.Rational)) _ (by decide)
  simpa only [Fraction.Field.mul_comm] using scaledStrict
end Purelib.Approximation.Gaussian.Enclosure.Sector.Large

end

section
@[expose] public section

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

namespace Purelib.Approximation.Gaussian.Enclosure.Sector.Large

/-- A passing unary-ball test makes the explicit candidate lower quadrance strictly greater than two. -/
theorem unaryCandidateLower_gt_two {ball :
    Approximation.Gaussian.Enclosure.Ball}
    (unary : UnaryBall ball) :
    2 < Ball.Bounds.unaryCandidateLower ball := by
  apply (Fraction.Order.Field.lt_div_iff_pos
    Ball.Bounds.sixteen_fifteenths_pos).2
  apply Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct
    (c := 16 * ball.radiusSq)
  calc
    2 * (16 / 15) + 16 * ball.radiusSq =
        (16 / 15) * 2 + 16 * ball.radiusSq := by ring1
    _ < Data.Gaussian.Norm.Basic.normSq ball.center := unary
    _ = (Data.Gaussian.Norm.Basic.normSq ball.center - 16 * ball.radiusSq) +
        16 * ball.radiusSq := by ring1
end Purelib.Approximation.Gaussian.Enclosure.Sector.Large

end
