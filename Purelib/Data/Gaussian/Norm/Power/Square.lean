module

public import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Root quadrance ceilings from actual square residuals

A fixed Gaussian coefficient and a paid square residual bound the original
reading's quadrance. The default rational ceiling is coefficient-computed;
smaller ceilings use only a checked bound on that exact coefficient.
-/

public section

namespace Purelib.Data.Gaussian.Norm.Power

open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- A positive rational ceiling computed from the actual Gaussian square parameter. -/
@[expose] def rootNormCeiling (parameter : Canonical) : Fraction.Rational :=
  2 * (1 + Norm.Basic.normSq parameter)

/-- The coefficient-computed root quadrance ceiling is strictly positive. -/
theorem rootNormCeiling_positive (parameter : Canonical) : 0 < rootNormCeiling parameter := by
  have positive := Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Norm.Basic.normSq_nonneg parameter) (by decide +kernel : (0 : Fraction.Rational) < 1)
  have reordered := positive.trans_eq (Fraction.Field.add_comm (Norm.Basic.normSq parameter) 1)
  exact Order.Arithmetic.mul_pos_direct (by decide +kernel) reordered

/-- The actual parameter quadrance pays one quarter of the computed ceiling's square. -/
theorem rootNormCeiling_parameter (parameter : Canonical) :
    Norm.Basic.normSq parameter ≤ rootNormCeiling parameter ^ 2 / 4 := by
  let value := Norm.Basic.normSq parameter
  have nonnegative : 0 ≤ (1 + value) ^ 2 - value := by
    have sum := Order.Arithmetic.add_le_add_direct
      (show (0 : Fraction.Rational) ≤ 1 + value from
        (show (0 : Fraction.Rational) = 0 + 0 by ring1).trans_le
          (Order.Arithmetic.add_le_add_direct (by decide +kernel) (Norm.Basic.normSq_nonneg parameter)))
      (Order.Arithmetic.sq_nonneg_direct value)
    exact (show (0 : Fraction.Rational) = 0 + 0 by ring1).trans_le (sum.trans_eq (by ring1))
  have bound : value ≤ (1 + value) ^ 2 := Order.Arithmetic.le_of_sub_nonneg_direct nonnegative
  have scalar : rootNormCeiling parameter ^ 2 / 4 = (1 + value) ^ 2 := by
    apply Fraction.Field.mul_right_cancel_of_ne (by decide +kernel : (4 : Fraction.Rational) ≠ 0)
    calc
      _ = rootNormCeiling parameter ^ 2 := Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide +kernel)
      _ = (1 + value) ^ 2 * 4 := by unfold rootNormCeiling; dsimp only [value]; ring1
  exact bound.trans_eq scalar.symm

/-- Two paid quarter-square bounds on the exact parameter and residual bound the original reading quadrance. -/
theorem root_normSq_le {value parameter : Canonical} {ceiling : Fraction.Rational}
    (nonnegative : 0 ≤ ceiling)
    (parameterBound : Norm.Basic.normSq parameter ≤ ceiling ^ 2 / 4)
    (residual : Norm.Basic.normSq (value * value - parameter) ≤ ceiling ^ 2 / 4) :
    Norm.Basic.normSq value ≤ ceiling := by
  have original := Norm.Bounds.value_normSq_le_of_offset residual
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct parameterBound
      (Fraction.Order.Basic.le_refl (ceiling ^ 2 / 4))) (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  have scalar : 2 * (ceiling ^ 2 / 4 + ceiling ^ 2 / 4) = ceiling ^ 2 :=
    (Fraction.Field.mul_comm _ _).trans
      ((show (ceiling ^ 2 / 4 + ceiling ^ 2 / 4) * 2 = (ceiling ^ 2 / 4) * 4 by ring1).trans
        (Fraction.Field.div_mul_cancel_of_ne _ 4 (by decide +kernel)))
  have power : Norm.Basic.normSq (value * value) = Norm.Basic.normSq value ^ 2 :=
    (congrArg Norm.Basic.normSq (show value * value = value ^ 2 by ring1)).trans (normSq_pow value 2)
  exact Order.Arithmetic.le_of_sq_le_sq_direct nonnegative
    (power.symm.trans_le (original.trans (scaled.trans_eq scalar)))

end Purelib.Data.Gaussian.Norm.Power

end
