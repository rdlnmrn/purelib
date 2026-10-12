module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
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

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat

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

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds

/-! ## Unary loop scaling -/

/-- Explicit candidate lower norm extracted from a unary-ball certificate. -/
def unaryCandidateLower (ball :
    Ball) :
  Fraction.Rational :=
  (Data.Gaussian.Norm.Basic.normSq ball.center - 16 * ball.radiusSq) / (16 / 15)

/-- The rational coefficient sixteen fifteenths is strictly positive. -/
public theorem sixteen_fifteenths_pos :
    (0 : Fraction.Rational) < 16 / 15 :=
  Fraction.Order.Field.div_pos_direct (by decide) (by decide)

/-- The explicit unary lower bound is at most the squared norm of every reading admitted by the ball. -/
theorem unaryCandidateLower_le {ball :
    Ball}
  {value : Data.Gaussian.Basic.Canonical}
    (inside : ball.Contains value) :
    unaryCandidateLower ball ≤ Data.Gaussian.Norm.Basic.normSq
      value := by
  have centerDecomposition :
      ball.center = (ball.center - value) + value := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.add_im] <;> ring1
  have errorNorm : Data.Gaussian.Norm.Basic.normSq (ball.center - value) ≤ ball.radiusSq := by
    have difference : ball.center - value = -(value - ball.center) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.neg_re,
          Data.Gaussian.Basic.neg_im] <;> ring1
    rw [difference, Data.Gaussian.Norm.Basic.normSq_neg]
    exact inside
  have centerUpper : Data.Gaussian.Norm.Basic.normSq ball.center ≤
      16 * ball.radiusSq + (16 / 15) * Data.Gaussian.Norm.Basic.normSq value := by
    rw [centerDecomposition]
    exact (Weighted.normSq_add_le_weighted
      (ball.center - value) value).trans
      (add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          errorNorm (by decide)) le_rfl)
  apply (Fraction.Order.Field.div_le_iff_pos
    sixteen_fifteenths_pos).2
  apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
    (c := 16 * ball.radiusSq)
  calc
    Data.Gaussian.Norm.Basic.normSq ball.center - 16 * ball.radiusSq + 16 * ball.radiusSq =
        Data.Gaussian.Norm.Basic.normSq ball.center := by ring1
    _ ≤ 16 * ball.radiusSq + (16 / 15) * Data.Gaussian.Norm.Basic.normSq value := centerUpper
    _ = Data.Gaussian.Norm.Basic.normSq value * (16 / 15) + 16 * ball.radiusSq := by ring1
end Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds

end

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

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds

/-- The explicit upper norm stored by a small residual ball. -/
def smallUpper (ball :
    Ball) : Fraction.Rational
  :=
  2 * (ball.radiusSq + Data.Gaussian.Norm.Basic.normSq ball.center)

end Purelib.Approximation.Gaussian.Enclosure.Ball.Bounds

end
