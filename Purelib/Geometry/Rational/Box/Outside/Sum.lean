module

public import Purelib.Geometry.Rational.Box.Outside
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Geometry.Rational.Box.Sum
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Sum separation from an original signed rational window

The midpoint of two readings in the same box remains in that box. An
existing outside-side certificate for zero therefore pays one quarter of
their sum quadrance. The original window, side and two readings are retained;
no common root or equality of readings is asserted.
-/

public section

namespace Purelib.Geometry.Rational.Box.OutsideSide

open Purelib.Data
open Purelib.Data.Rat

/-- Two readings in an original zero-separated box have a quantitatively separated sum. -/
theorem sum_normSq_lower {box : Rational.Box} (side : OutsideSide box 0)
    {first last : Gaussian.Basic.Canonical} (firstInside : box.Contains first) (lastInside : box.Contains last) :
    4 * side.margin ≤ Gaussian.Norm.Basic.normSq (first + last) :=
  Box.sum_normSq_lower box side.margin (fun inside => by
    have lower := side.margin_le_normSq_sub inside
    rewrite [Gaussian.Basic.sub_zero] at lower
    exact lower) firstInside lastInside

/-- The same original outside side makes the two contained readings' sum nonzero. -/
theorem sum_nonzero {box : Rational.Box} (side : OutsideSide box 0)
    {first last : Gaussian.Basic.Canonical} (firstInside : box.Contains first) (lastInside : box.Contains last) :
    first + last ≠ 0 := by
  have positive : 0 < 4 * side.margin :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) side.margin_pos
  intro zero
  have lower := side.sum_normSq_lower firstInside lastInside
  rewrite [zero, Gaussian.Norm.Basic.normSq_zero] at lower
  exact (not_le_of_gt positive) lower

end Purelib.Geometry.Rational.Box.OutsideSide
