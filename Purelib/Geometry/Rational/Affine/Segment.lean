module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Affine
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Gaussian.Cast

open Purelib.Data.Rat

open Purelib.Geometry.Rational

/-!
# Rational affine segments

Endpoint, displacement and rotation laws use the segment from `start` to
`finish`, parameterized by their retained difference.
-/

public section

namespace Purelib.Geometry.Rational.Affine.Segment

open Purelib.Data.Gaussian

/-- An affine segment whose endpoints coincide is constant. -/
@[simp] theorem line_self (point : Data.Gaussian.Basic.Canonical) (time
  : Fraction.Rational) :
    Affine.line point (point - point) time = point := by
  rw [sub_self]
  change point + Path.ofCoordinate time * 0 = point
  rw [mul_zero, add_zero]

/-- A segment evaluated at parameter zero is its start. -/
@[simp] theorem line_segment_zero (start finish :
  Data.Gaussian.Basic.Canonical) :
    Affine.line start (finish - start) 0 = start := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [Affine.line, Path.ofCoordinate, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
      Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im] <;>
    ring1

/-- A segment evaluated at parameter one is its finish. -/
@[simp] theorem line_segment_one (start finish :
  Data.Gaussian.Basic.Canonical) :
    Affine.line start (finish - start) 1 = finish := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [Affine.line, Path.ofCoordinate, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
      Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im] <;>
    ring1

/-- A point on the displayed parameter segment is no farther from its source than the displayed endpoint displacement.
-/
theorem normSq_source_sub_line_le
    (source target : Data.Gaussian.Basic.Canonical) {time : Fraction.Rational}
    (timeInside : (0 : Fraction.Rational) ≤ time ∧ time ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (source -
        Affine.line source (target - source) time) ≤
      Data.Gaussian.Norm.Basic.normSq (source - target) := by
  have identity :
      source - Affine.line source (target - source) time =
        Path.ofCoordinate time * (source - target) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Affine.line, Data.Gaussian.Cast.ofCoordinate_re,
        Data.Gaussian.Cast.ofCoordinate_im, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
          Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im,
        Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im] <;>
      ring1
  have timeSquareLeOne : time ^ 2 ≤ (1 : Fraction.Rational) := by
    have powered := Fraction.Order.Arithmetic.pow_le_pow_direct timeInside.1
      timeInside.2 2
    simpa only [one_pow] using powered
  rw [identity, Data.Gaussian.Norm.Basic.normSq_mul]
  have scalarNorm :
      Data.Gaussian.Norm.Basic.normSq (Path.ofCoordinate time) = time ^ 2 := by
    simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Cast.ofCoordinate_re,
      Data.Gaussian.Cast.ofCoordinate_im]
    ring1
  rw [scalarNorm]
  calc
    time ^ 2 * Data.Gaussian.Norm.Basic.normSq (source - target) ≤
        1 * Data.Gaussian.Norm.Basic.normSq (source - target) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        timeSquareLeOne (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    _ = Data.Gaussian.Norm.Basic.normSq (source - target) := by ring1

/-- Rotation carries the real coordinate of an affine segment to the corresponding affine combination.

The identity holds for every rational parameter; no interval restriction is required. -/
theorem rotated_line_real_eq_convex
    (rotation source target : Data.Gaussian.Basic.Canonical) (time : Fraction.Rational) :
    (rotation * Affine.line source (target - source) time).re =
      (1 - time) * (rotation * source).re +
        time * (rotation * target).re := by
  simp only [Affine.line,
    Data.Gaussian.Cast.ofCoordinate_re,
    Data.Gaussian.Cast.ofCoordinate_im,
    Data.Gaussian.Basic.mul_re,
    Data.Gaussian.Basic.mul_im,
    Data.Gaussian.Basic.add_re,
    Data.Gaussian.Basic.add_im,
    Data.Gaussian.Basic.sub_re,
    Data.Gaussian.Basic.sub_im]
  ring1

end Purelib.Geometry.Rational.Affine.Segment
