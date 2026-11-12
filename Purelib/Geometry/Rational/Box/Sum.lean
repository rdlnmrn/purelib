module

public import Purelib.Geometry.Rational.Box.Segment
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Sum separation from the same original convex rational box

A common lower quadrance on every point of one original box also bounds the
midpoint of two contained readings. Multiplying its quadrance by four gives
an explicit lower bound on their sum, without selecting or replacing either
reading or requiring a coordinate-side separation certificate.
-/

public section

namespace Purelib.Geometry.Rational.Box

open Purelib.Data
open Purelib.Data.Rat

/-- A uniform lower quadrance on an original box pays four times that bound for sums of two contained readings. -/
theorem sum_normSq_lower (box : Rational.Box) (floor : Fraction.Rational)
    (bounded : ∀ {value : Gaussian.Basic.Canonical}, box.Contains value → floor ≤ Gaussian.Norm.Basic.normSq value)
    {first last : Gaussian.Basic.Canonical} (firstInside : box.Contains first) (lastInside : box.Contains last) :
    4 * floor ≤ Gaussian.Norm.Basic.normSq (first + last) := by
  let half := Gaussian.Cast.Path.ofCoordinate (1 / 2)
  have halfDouble : half * 2 = (1 : Gaussian.Basic.Canonical) := by decide +kernel
  have midpointEq : Rational.Affine.line first (last - first) (1 / 2) = (first + last) * half := by
    apply Gaussian.Field.mul_right_cancel_of_ne (by decide +kernel : (2 : Gaussian.Basic.Canonical) ≠ 0)
    calc
      _ = first * 2 + (half * 2) * (last - first) := by
        unfold Rational.Affine.line
        change (first + half * (last - first)) * 2 = _
        ring1
      _ = first + last := by rewrite [halfDouble, Gaussian.Basic.one_mul]; ring1
      _ = ((first + last) * half) * 2 := by
        rewrite [Gaussian.Basic.mul_assoc, halfDouble, Gaussian.Basic.mul_one]
        rfl
  have midpointInside := Box.contains_line firstInside lastInside (by decide +kernel :
    (0 : Fraction.Rational) ≤ 1 / 2 ∧ (1 / 2 : Fraction.Rational) ≤ 1)
  rewrite [midpointEq] at midpointInside
  have lower := bounded midpointInside
  rewrite [Gaussian.Norm.Basic.normSq_mul,
    show Gaussian.Norm.Basic.normSq half = (1 / 4 : Fraction.Rational) by decide +kernel] at lower
  calc
    _ ≤ 4 * (Gaussian.Norm.Basic.normSq (first + last) * (1 / 4)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower (by decide +kernel)
    _ = _ := by
      calc
        _ = Gaussian.Norm.Basic.normSq (first + last) * (4 * (1 / 4)) := by ring1
        _ = _ := by rewrite [show (4 : Fraction.Rational) * (1 / 4) = 1 by decide +kernel,
          Fraction.Field.mul_one_direct]; rfl

end Purelib.Geometry.Rational.Box

end
