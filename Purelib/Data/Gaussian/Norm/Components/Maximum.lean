module

public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Abs
public import Purelib.Data.Gaussian.Scale
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # The maximum absolute coordinate of a Gaussian rational

The executable maximum retains one of the two original absolute coordinates.
Its square lies between one half of the original quadrance and that quadrance,
so it provides rational square widths without obtaining a square root.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Components

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_right)

/-- The greater of the two original absolute Gaussian coordinates. -/
@[expose] def maximum (value : Canonical) : Fraction.Rational :=
  max (Fraction.abs value.re) (Fraction.abs value.im)

/-- The retained maximum absolute coordinate is nonnegative. -/
theorem maximum_nonnegative (value : Canonical) : 0 ≤ maximum value :=
  (Arithmetic.abs_nonneg_direct value.re).trans (Fraction.Order.Basic.le_max_left _ _)

/-- The original real coordinate's absolute value is bounded by the retained maximum. -/
theorem abs_re_le_maximum (value : Canonical) : Fraction.abs value.re ≤ maximum value :=
  Fraction.Order.Basic.le_max_left _ _

/-- The original imaginary coordinate's absolute value is bounded by the retained maximum. -/
theorem abs_im_le_maximum (value : Canonical) : Fraction.abs value.im ≤ maximum value :=
  Fraction.Order.Basic.le_max_right _ _

/-- The square of the retained maximum is bounded by the original Gaussian quadrance. -/
theorem maximum_sq_le_normSq (value : Canonical) : maximum value ^ 2 ≤ Basic.normSq value := by
  change (if Fraction.abs value.re ≤ Fraction.abs value.im then Fraction.abs value.im else
    Fraction.abs value.re) ^ 2 ≤ value.re ^ 2 + value.im ^ 2
  by_cases ordered : Fraction.abs value.re ≤ Fraction.abs value.im
  · rewrite [if_pos ordered, Rat.Bounds.Abs.abs_sq_direct]
    exact (show value.im ^ 2 = 0 + value.im ^ 2 from (Fraction.Field.zero_add _).symm).trans_le
      (Arithmetic.add_le_add_direct (Arithmetic.sq_nonneg_direct value.re)
        (Fraction.Order.Basic.le_refl _))
  · rewrite [if_neg ordered, Rat.Bounds.Abs.abs_sq_direct]
    exact (show value.re ^ 2 = value.re ^ 2 + 0 from by ring1).trans_le
      (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (Arithmetic.sq_nonneg_direct value.im))

/-- Twice the square of the retained maximum bounds the original Gaussian quadrance. -/
theorem normSq_le_twice_maximum_sq (value : Canonical) : Basic.normSq value ≤ 2 * maximum value ^ 2 := by
  have real := Arithmetic.pow_le_pow_direct (Arithmetic.abs_nonneg_direct value.re)
    (abs_re_le_maximum value) 2
  have imaginary := Arithmetic.pow_le_pow_direct
    (Arithmetic.abs_nonneg_direct value.im) (abs_im_le_maximum value) 2
  rewrite [Rat.Bounds.Abs.abs_sq_direct] at real imaginary
  exact (Arithmetic.add_le_add_direct real imaginary).trans_eq (by ring1)

/-- A nonzero Gaussian rational has a strictly positive retained maximum absolute coordinate. -/
theorem maximum_positive {value : Canonical} (nonzero : value ≠ 0) : 0 < maximum value := by
  have nonnegative := maximum_nonnegative value
  refine ⟨nonnegative, ?_⟩
  intro reverse
  have zero := Fraction.Order.Basic.le_antisymm _ _ reverse nonnegative
  have norm := normSq_le_twice_maximum_sq value
  rewrite [zero, show 2 * (0 : Fraction.Rational) ^ 2 = 0 by decide +kernel] at norm
  exact (Basic.normSq_pos nonzero).2 norm

/-- Nonnegative rational scaling preserves the retained maximum absolute coordinate exactly.

The same scale multiplies both original coordinates. The owned absolute
product law and rational comparison decide which original coordinate
attains the maximum, including scale zero and a zero original vector.
-/
theorem maximum_scale (factor : Fraction.Rational) (nonnegative : 0 ≤ factor) (value : Canonical) :
    maximum (Scale.scale factor value) = factor * maximum value := by
  have real : Fraction.abs (Scale.scale factor value).re = factor * Fraction.abs value.re :=
    (Rat.Bounds.Abs.abs_mul_direct factor value.re).trans
      (congrArg (fun scalar : Fraction.Rational => scalar * Fraction.abs value.re)
        (Rat.Bounds.Abs.abs_of_nonnegative nonnegative))
  have imaginary : Fraction.abs (Scale.scale factor value).im = factor * Fraction.abs value.im :=
    (Rat.Bounds.Abs.abs_mul_direct factor value.im).trans
      (congrArg (fun scalar : Fraction.Rational => scalar * Fraction.abs value.im)
        (Rat.Bounds.Abs.abs_of_nonnegative nonnegative))
  have coordinates := congrArg₂
    (fun real imaginary : Fraction.Rational => max real imaginary) real imaginary
  unfold maximum
  rcases Fraction.Order.Basic.le_total (Fraction.abs value.re) (Fraction.abs value.im) with ordered | ordered
  · have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct ordered nonnegative
    exact coordinates.trans ((Fraction.Order.Basic.max_eq_right scaled).trans
      (congrArg (fun scalar : Fraction.Rational => factor * scalar)
        (Fraction.Order.Basic.max_eq_right ordered)).symm)
  · have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct ordered nonnegative
    exact coordinates.trans ((Fraction.Order.Basic.max_eq_left scaled).trans
      (congrArg (fun scalar : Fraction.Rational => factor * scalar)
        (Fraction.Order.Basic.max_eq_left ordered)).symm)

/-- A finite family of nonnegative scales retains the original total maximum-coordinate variation.

Every original occurrence is included. Zero scales contribute zero, and
there is no division by a scale or assumption of strict progress.
-/
theorem sum_maximum_scales {count : Nat} (factors : Fin count → Fraction.Rational)
    (nonnegative : ∀ index, 0 ≤ factors index) (value : Canonical) :
    sumFin (fun index => maximum (Scale.scale (factors index) value)) =
      sumFin factors * maximum value :=
  (sumFin_congr (fun index =>
    maximum_scale (factors index) (nonnegative index) value)).trans
      (sumFin_mul_right factors (maximum value))

end Purelib.Data.Gaussian.Norm.Components
