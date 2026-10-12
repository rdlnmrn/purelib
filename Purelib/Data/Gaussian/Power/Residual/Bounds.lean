module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import all Purelib.Data.Rat.Fraction.Power.Order

import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Data.Gaussian.Power.Residual.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A positive power exponent, unit parameter and quarter-bounded residual bound the point squared norm by five halves.
-/
private theorem normSq_le_five_halves_of_power_residual
    {parameter point : Basic.Canonical} {exponent : Nat}
    (exponentPositive : 0 < exponent)
    (parameterUnit : Norm.Basic.normSq parameter = 1)
    (residualSmall : Norm.Basic.normSq (point ^ exponent - parameter) ≤
      (1 / 4 : Fraction.Rational)) :
    Norm.Basic.normSq point ≤ 5 / 2 := by
  let residual := point ^ exponent - parameter
  have sumIdentity : point ^ exponent = residual + parameter := by
    apply Basic.ext <;>
      simp only [residual, Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im] <;>
      ring1
  have powerUpper : Norm.Basic.normSq point ^ exponent ≤ (5 / 2 : Fraction.Rational) := by
    calc
      Norm.Basic.normSq point ^ exponent = Norm.Basic.normSq (point ^ exponent) :=
        (Power.normSq_pow point exponent).symm
      _ = Norm.Basic.normSq (residual + parameter) := by rw [sumIdentity]
      _ ≤ 2 * (Norm.Basic.normSq residual + Norm.Basic.normSq parameter) :=
        Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * ((1 / 4 : Fraction.Rational) + 1) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add residualSmall parameterUnit.le) (by decide)
      _ = 5 / 2 := by decide
  exact Fraction.Power.Order.value_le_five_halves_of_power_le exponentPositive
    (Norm.Basic.normSq_nonneg point) powerUpper
end Purelib.Data.Gaussian.Power.Residual.Bounds

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Data.Gaussian.Power.Residual.Bounds

/-! ## Uniform derivative separation on the unit parameter circuit -/

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A unit parameter is bounded by twice the sum of the power norm and its residual norm. -/
private theorem unit_le_twice_power_add_residual
    {parameter point : Basic.Canonical} {exponent : Nat}
    (parameterUnit : Norm.Basic.normSq parameter = 1) :
    (1 : Fraction.Rational) ≤
      2 * (Norm.Basic.normSq (point ^ exponent) +
        Norm.Basic.normSq (point ^ exponent - parameter)) := by
  have raw := Norm.Bounds.normSq_sub_le_two
    (point ^ exponent) (point ^ exponent - parameter)
  have identity : point ^ exponent - (point ^ exponent - parameter) =
      parameter := by
    apply Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im] <;>
      ring1
  rw [identity, parameterUnit] at raw
  exact raw
end Purelib.Data.Gaussian.Power.Residual.Bounds

end

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.Data.Gaussian.Power.Residual.Bounds

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A quarter-bounded residual from a unit parameter forces the powered point norm to be at least one quarter. -/
private theorem one_fourth_le_normSq_power_of_residual_le_quarter
    {parameter point : Basic.Canonical} {exponent : Nat}
    (parameterUnit : Norm.Basic.normSq parameter = 1)
    (residualSmall : Norm.Basic.normSq (point ^ exponent - parameter) ≤
      (1 / 4 : Fraction.Rational)) :
    (1 / 4 : Fraction.Rational) ≤ Norm.Basic.normSq point ^ exponent := by
  have sumBound :
      Norm.Basic.normSq (point ^ exponent) +
          Norm.Basic.normSq (point ^ exponent - parameter) ≤
        Norm.Basic.normSq (point ^ exponent) + (1 / 4 : Fraction.Rational) := by
    calc
      Norm.Basic.normSq (point ^ exponent) + Norm.Basic.normSq (point ^ exponent - parameter) =
          Norm.Basic.normSq (point ^ exponent - parameter) +
            Norm.Basic.normSq (point ^ exponent) := by ring1
      _ ≤ (1 / 4 : Fraction.Rational) + Norm.Basic.normSq (point ^ exponent) :=
        Fraction.Order.Arithmetic.add_le_add_right_direct residualSmall _
      _ = Norm.Basic.normSq (point ^ exponent) + (1 / 4 : Fraction.Rational) := by ring1
  have bounded : (1 : Fraction.Rational) ≤
      2 * (Norm.Basic.normSq (point ^ exponent) + (1 / 4 : Fraction.Rational)) :=
    (unit_le_twice_power_add_residual parameterUnit).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        sumBound (by decide))
  have lower := Fraction.Power.Order.one_fourth_le_of_unit_triangle bounded
  simpa only [Power.normSq_pow] using lower
end Purelib.Data.Gaussian.Power.Residual.Bounds

end
