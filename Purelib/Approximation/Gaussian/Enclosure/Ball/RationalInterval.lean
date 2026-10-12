module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Data

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# One-sided rational pairs as ordinary CCL processes

This CCL-side bridge converts a lower/upper rational pair only when it carries
the explicit finite gap modulus in `FiniteMeasure.LocatedPair`.  The bare
one-sided processes remain rate-free.

The requested CCL squared-error target is translated to the strictly smaller
rational gap `target / (target + 1)`.  Its square is below `target`, so the
construction needs no square root, completion, limit, or unbounded search.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.RationalInterval

/-- A rational interval as a real-axis Gaussian ball. The lower endpoint is the canonical centre and the interval width
supplies a square error bound. -/
def ballOfBound (bound : Rat.Interval) :
  Approximation.Gaussian.Enclosure.Ball where
  center := RationalEmbedding.realPoint bound.sample
  radiusSq := bound.width ^ 2
  radiusSq_nonneg := Fraction.Order.Arithmetic.sq_nonneg_direct bound.width

/-- The real coordinate of the interval ball's centre is the original interval sample. -/
@[simp] theorem ballOfBound_center_re (bound :
  Rat.Interval) :
    (ballOfBound bound).center.re = bound.sample :=
  rfl

/-- The imaginary coordinate of the interval ball's centre is zero. -/
@[simp] theorem ballOfBound_center_im (bound :
  Rat.Interval) :
    (ballOfBound bound).center.im = 0 :=
  rfl

/-- The interval ball's squared radius is the square of the original interval width. -/
@[simp] theorem ballOfBound_radiusSq (bound :
  Rat.Interval) :
    (ballOfBound bound).radiusSq = bound.width ^ 2 :=
  rfl

/-- Every displayed rational admitted by the interval is admitted by its real-axis Gaussian ball. -/
theorem ballOfBound_contains {bound :
  Rat.Interval}
    {value : Fraction.Rational} (inside : bound.Contains value) :
    (ballOfBound bound).Contains (RationalEmbedding.realPoint
      value) := by
  unfold Approximation.Gaussian.Enclosure.Ball.Contains
  rw [show (ballOfBound bound).center =
    RationalEmbedding.realPoint bound.sample by rfl,
    RationalEmbedding.realPoint_sub, RationalEmbedding.normSq_realPoint]
  have directed := Interval.sample_difference_le inside
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (bound.width - (value - bound.sample)) *
          (bound.width + (value - bound.sample)) := by
      apply Fraction.Order.Arithmetic.mul_nonneg_direct
      · exact Fraction.Order.Arithmetic.sub_nonneg_direct directed.1
      · have nonnegative :
          0 ≤ bound.width - (bound.sample - value) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct directed.2
        calc
          0 ≤ bound.width - (bound.sample - value) := nonnegative
          _ = bound.width + (value - bound.sample) := by ring1
    _ = bound.width ^ 2 - (value - bound.sample) ^ 2 := by ring1

/-- A coarse explicit bound for every later real-axis ball centre, obtained from containment in one displayed outer
interval. -/
theorem ballOfBound_center_bounded {inner outer :
  Rat.Interval}
    (refines : Interval.Refines inner outer) :
    Data.Gaussian.Norm.Basic.normSq (ballOfBound
      inner).center ≤
      2 * (Data.Gaussian.Norm.Basic.normSq (RationalEmbedding.realPoint outer.sample) + outer.width ^ 2) := by
  have sampleInside : outer.Contains inner.sample :=
    refines.contains inner.sample_contains
  have differenceInside :
      Data.Gaussian.Norm.Basic.normSq (RationalEmbedding.realPoint inner.sample - RationalEmbedding.realPoint
        outer.sample) ≤
        outer.width ^ 2 := by
    simpa only [ballOfBound,
        Approximation.Gaussian.Enclosure.Ball.Contains] using
      ballOfBound_contains sampleInside
  have decomposition :
      RationalEmbedding.realPoint inner.sample = RationalEmbedding.realPoint outer.sample +
        (RationalEmbedding.realPoint inner.sample - RationalEmbedding.realPoint outer.sample) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [RationalEmbedding.realPoint_re, RationalEmbedding.realPoint_im, Basic.add_re, Basic.add_im,
        Basic.sub_re, Basic.sub_im] <;>
      ring1
  rw [show (ballOfBound inner).center =
    RationalEmbedding.realPoint inner.sample by rfl,
    decomposition]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl differenceInside) (by decide))
end Purelib.Approximation.Gaussian.Enclosure.Ball.RationalInterval

end
