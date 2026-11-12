module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Bounds.Abs
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Gaussian coordinate and squared-norm bounds

Finite rational bounds on the real and imaginary displacements determine a
bound on their combined Gaussian squared norm, and each squared coordinate is
bounded by that norm.
-/

namespace Purelib.Data.Gaussian.Norm.Coordinates

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- A rational absolute-value bound also bounds the square by the square of the same budget. -/
theorem square_le_of_abs_le {value bound : Fraction.Rational} (bounded : Fraction.abs value ≤ bound) :
    value ^ 2 ≤ bound ^ 2 := by
  have nonnegative := Arithmetic.abs_nonneg_direct value
  have boundNonnegative := nonnegative.trans bounded
  have product := Arithmetic.mul_le_mul_direct bounded bounded nonnegative boundNonnegative
  rw [← pow_two, ← pow_two, Bounds.Abs.abs_sq_direct] at product
  exact product

/-- Coordinate error budgets add as squares to bound the original Gaussian squared displacement. -/
theorem sub_normSq_le (value center : Basic.Canonical) (realBudget imaginaryBudget : Fraction.Rational)
    (realBound : Fraction.abs (value.re - center.re) ≤ realBudget)
    (imaginaryBound : Fraction.abs (value.im - center.im) ≤ imaginaryBudget) :
    Norm.Basic.normSq (value - center) ≤ realBudget ^ 2 + imaginaryBudget ^ 2 := by
  have sum := Arithmetic.add_le_add_direct
    (square_le_of_abs_le realBound) (square_le_of_abs_le imaginaryBound)
  change (value.re - center.re) ^ 2 + (value.im - center.im) ^ 2 ≤ _
  exact sum

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The squared real-coordinate displacement is at most the full Gaussian squared displacement. -/
public theorem re_sub_sq_le_normSq (value center : Basic.Canonical) :
    (value.re - center.re) ^ 2 ≤ Basic.Canonical.normSq (value - center) := by
  rw [Basic.Canonical.normSq]
  simp only [Basic.sub_re, Basic.sub_im]
  rw [← pow_two, ← pow_two]
  exact le_add_of_nonneg_right
    (Arithmetic.sq_nonneg_direct (value.im - center.im))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The squared imaginary-coordinate displacement is at most the full Gaussian squared displacement. -/
public theorem im_sub_sq_le_normSq (value center : Basic.Canonical) :
    (value.im - center.im) ^ 2 ≤ Basic.Canonical.normSq (value - center) := by
  rw [Basic.Canonical.normSq]
  simp only [Basic.sub_re, Basic.sub_im]
  rw [← pow_two, ← pow_two]
  have bound := Arithmetic.add_le_add_direct
    (Arithmetic.sq_nonneg_direct (value.re - center.re))
    (le_rfl : (value.im - center.im) ^ 2 ≤ (value.im - center.im) ^ 2)
  rw [Fraction.Field.zero_add] at bound
  exact bound

open Purelib.Data.Gaussian in
/-- The squared real displacement is bounded by the power-form Gaussian norm. -/
public theorem re_sub_sq_le_basic_normSq (value center : Basic.Canonical) :
    (value.re - center.re) ^ 2 ≤ Basic.normSq (value - center) := by
  rw [Basic.normSq_eq_canonical]
  exact re_sub_sq_le_normSq value center

open Purelib.Data.Gaussian in
/-- The squared imaginary displacement is bounded by the power-form Gaussian norm. -/
public theorem im_sub_sq_le_basic_normSq (value center : Basic.Canonical) :
    (value.im - center.im) ^ 2 ≤ Basic.normSq (value - center) := by
  rw [Basic.normSq_eq_canonical]
  exact im_sub_sq_le_normSq value center

end Purelib.Data.Gaussian.Norm.Coordinates

end
