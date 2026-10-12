module
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Scale-sensitive bounds for finite square-root readings

A squared radicand lower bound is used at its original linear scale. This
retains the power of the geometric radius needed on shrinking boundaries;
no real square root or new root-selection procedure is introduced.
-/

namespace Purelib.Riemann.RootContinuation.ScaledRootBounds

open Purelib.Data.Gaussian.Basic.Canonical Purelib.Riemann.Branches.SquareRootSheets

section
open Purelib.Data.Rat
/-- A scale whose square is bounded by the original radicand norm is at most four times its retained sample lower bound.

The exact coordinate norm estimate and original sample-lower formula give the direct rational bound. -/
theorem scale_le_four_sampleNormLower {parameter : Gaussian} {scale : Coordinate}
    (squared : scale ^ 2 ≤ normSq parameter) : scale ≤ 4 * sampleNormLower parameter := by
  have coordinateNonnegative : 0 ≤ coordinateNormLower parameter :=
    (Fraction.Order.Arithmetic.abs_nonneg_direct parameter.re).trans (Fraction.Order.Basic.le_max_left _ _)
  have scaleBound : scale ≤ 2 * coordinateNormLower parameter := by
    apply Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) coordinateNonnegative)
    calc
      scale ^ 2 ≤ normSq parameter := squared
      _ ≤ 2 * coordinateNormLower parameter ^ 2 := normSq_le_two_coordinateNormLower_sq parameter
      _ ≤ 2 * coordinateNormLower parameter ^ 2 + 2 * coordinateNormLower parameter ^ 2 :=
        le_add_of_nonneg_right (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      _ = (2 * coordinateNormLower parameter) ^ 2 := by ring1
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Basic.le_max_right (min 1 (residualTarget parameter)) (coordinateNormLower parameter / 2)) (by
      decide : (0 : Coordinate) ≤ 4)
  have equal : 4 * (coordinateNormLower parameter / 2) = 2 * coordinateNormLower parameter := by
    have cancel := Fraction.Field.div_mul_cancel_of_ne (coordinateNormLower parameter) 2 (by decide)
    calc
      _ = 2 * ((coordinateNormLower parameter / 2) * 2) := by ring1
      _ = _ := congrArg (2 * ·) cancel
  exact scaleBound.trans (equal.symm.le.trans paid)

/-- The retained scale is at most four times a Gaussian sample norm satisfying the original root lower bound. -/
theorem scale_le_four_normSq {parameter value : Gaussian} {scale : Coordinate}
    (squared : scale ^ 2 ≤ normSq parameter) (lower : sampleNormLower parameter ≤ normSq value) :
    scale ≤ 4 * normSq value :=
  (scale_le_four_sampleNormLower squared).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower (by decide))

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A positive scale bounded by four times the denominator norm bounds the scaled quotient norm by four times the
numerator norm.

The original positive scale proves the denominator nonzero, allowing exact Gaussian norm division and rational
cancellation. -/
theorem scaled_quotient_bound {value : Gaussian} {scale : Coordinate} (positive : 0 < scale)
    (lower : scale ≤ 4 * normSq value) (numerator : Gaussian) :
    scale * normSq (numerator / value) ≤ 4 * normSq numerator := by
  have nonzero : value ≠ 0 := by
    intro zero
    rw [zero, Basic.Canonical.normSq_zero, Fraction.Field.mul_zero_direct] at lower
    exact (not_lt_of_ge lower) positive
  have normPositive := Norm.Basic.normSq_pos nonzero
  rw [Norm.Basic.normSq_eq_canonical] at normPositive
  have normNonzero := normPositive.ne'
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct lower (Basic.Canonical.normSq_nonneg
    (numerator / value))
  apply estimate.trans_eq
  rw [Basic.Canonical.normSq_div _ _ nonzero]
  calc
    (4 * normSq value) * (normSq numerator / normSq value) =
        4 * ((normSq numerator / normSq value) * normSq value) := by ring1
    _ = _ := congrArg (4 * ·) (Fraction.Field.div_mul_cancel_of_ne _ _ normNonzero)

end Purelib.Riemann.RootContinuation.ScaledRootBounds
