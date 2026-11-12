module

public import Purelib.Riemann.RootContinuation.SquareRootProvenance.Movement
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

/-! # Signed-box residual payment for actual root trace readings

A uniform squared-root norm floor fixes both the residual request and the
radicand movement request. The difference-of-squares estimate then pays the
original trace-edge relative distance threshold with the actual first norm.
No endpoint root agreement or equality of the two radicands is an input.
-/

public section

namespace Purelib.Riemann.RootContinuation.SquareRootProvenance

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Cast (natCast_eq_fromInt)

/-- The exact common quadrance request for square residuals and radicand movement. -/
@[expose] def traceAllowance (lower : Rational) : Rational := lower ^ 2 / 8192

/-- A positive squared-root norm floor gives a strictly positive actual residual and movement request. -/
theorem traceAllowance_positive {lower : Rational} (positive : 0 < lower) : 0 < traceAllowance lower :=
  Order.Field.div_pos_direct (Order.Arithmetic.pow_pos_direct positive 2) (by
    change (0 : Rational) < ((8192 : Nat) : Rational)
    rewrite [natCast_eq_fromInt 8192]
    decide +kernel)

/-- Both actual square residuals and radicand movement at the common request pay the trace relative-distance bound.

The sum floor is four times the same positive root-norm floor. Exact
rational scaling gives 5/16384 times that floor, which is no larger than
the original one-one-thousand-twenty-fourth trace threshold.
-/
theorem trace_distance_le (first last firstParameter lastParameter : Canonical)
    {lower : Rational} (positive : 0 < lower)
    (firstLower : lower ≤ Norm.Basic.normSq first)
    (sumLower : 4 * lower ≤ Norm.Basic.normSq (first + last))
    (firstResidual : Norm.Basic.normSq (first * first - firstParameter) ≤ traceAllowance lower)
    (movement : Norm.Basic.normSq (firstParameter - lastParameter) ≤ traceAllowance lower)
    (lastResidual : Norm.Basic.normSq (last * last - lastParameter) ≤ traceAllowance lower) :
    Norm.Basic.normSq (last - first) ≤ Norm.Basic.normSq first / 1024 := by
  have denominatorPositive : 0 < 4 * lower :=
    Order.Arithmetic.mul_pos_direct (by decide +kernel) positive
  have displaced := root_difference_le first last firstParameter lastParameter denominatorPositive sumLower
    firstResidual movement lastResidual
  have numeratorBound : 2 * (traceAllowance lower + 2 * (traceAllowance lower + traceAllowance lower)) ≤
      (lower / 1024) * (4 * lower) := by
    have coefficients : (10 : Rational) * 8192⁻¹ ≤ 4 * 1024⁻¹ := by
      change ((10 : Nat) : Rational) * (((8192 : Nat) : Rational))⁻¹ ≤
        ((4 : Nat) : Rational) * (((1024 : Nat) : Rational))⁻¹
      rewrite [natCast_eq_fromInt 10, natCast_eq_fromInt 8192, natCast_eq_fromInt 4,
        natCast_eq_fromInt 1024]
      decide +kernel
    have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficients
      (Order.Arithmetic.sq_nonneg_direct lower)
    calc
      _ = ((10 : Rational) * 8192⁻¹) * lower ^ 2 := by
        simp only [traceAllowance, Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
        ring1
      _ ≤ (4 * 1024⁻¹) * lower ^ 2 := scaled
      _ = (lower / 1024) * (4 * lower) := by
        rewrite [Field.div_eq_mul_inv_direct]
        ring1
  have multiplied : Norm.Basic.normSq (first - last) * (4 * lower) ≤
      (Norm.Basic.normSq first / 1024) * (4 * lower) := by
    calc
      _ ≤ (2 * (traceAllowance lower + 2 * (traceAllowance lower + traceAllowance lower)) /
          (4 * lower)) * (4 * lower) :=
        Order.Arithmetic.mul_le_mul_of_nonneg_right_direct displaced denominatorPositive.le
      _ = 2 * (traceAllowance lower + 2 * (traceAllowance lower + traceAllowance lower)) :=
        Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
      _ ≤ (lower / 1024) * (4 * lower) := numeratorBound
      _ ≤ _ := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Order.Field.divide_mono firstLower (by
          change (0 : Rational) < ((1024 : Nat) : Rational)
          rewrite [natCast_eq_fromInt 1024]
          decide +kernel)) denominatorPositive.le
  have bound := Order.Arithmetic.le_of_mul_le_mul_right_direct (c := 4 * lower) multiplied denominatorPositive
  exact (Norm.Bounds.normSq_sub_symm last first).trans_le bound

end Purelib.Riemann.RootContinuation.SquareRootProvenance

end
