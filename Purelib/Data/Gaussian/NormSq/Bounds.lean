module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Quadratic.Bounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.Data.Gaussian.NormSq

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- A positive lower margin for a Gaussian squared norm proves the Gaussian nonzero. -/
theorem denominator_ne_of_margin
    {denominatorMargin : Fraction.Rational} (marginPositive : 0 < denominatorMargin)
    {denominatorValue : Basic.Canonical}
    (lower : denominatorMargin ≤ Data.Gaussian.Norm.Basic.normSq denominatorValue) :
    denominatorValue ≠ 0 := by
  intro zero
  have positive : 0 < Data.Gaussian.Norm.Basic.normSq denominatorValue := marginPositive.trans_le lower
  rw [zero, Norm.Basic.normSq_zero] at positive
  exact (lt_irrefl 0 positive).elim

/-- A squared-norm bound places each Gaussian coordinate between the negative and positive values of bound plus one.

The radius used here is the supplied squared-norm bound plus one. No separately chosen square root or positive-radius
witness is required. -/
theorem coordinate_bounds_of_normSq_le
    (value : Basic.Canonical) {bound : Fraction.Rational} (normBound : Data.Gaussian.Norm.Basic.normSq value ≤ bound) :
    - (bound + 1) ≤ value.re ∧ value.re ≤ bound + 1 ∧
      - (bound + 1) ≤ value.im ∧ value.im ≤ bound + 1 := by
  have realSquare : value.re ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq value := by
    have added := Fraction.Order.Arithmetic.add_le_add_right_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct value.im) (value.re ^ 2)
    calc
      value.re ^ 2 = 0 + value.re ^ 2 :=
        (Fraction.Field.zero_add _).symm
      _ ≤ value.im ^ 2 + value.re ^ 2 := added
      _ = Data.Gaussian.Norm.Basic.normSq value := Fraction.Field.add_comm _ _
  have imaginarySquare : value.im ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq value := by
    have added := Fraction.Order.Arithmetic.add_le_add_right_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct value.re) (value.im ^ 2)
    calc
      value.im ^ 2 = 0 + value.im ^ 2 :=
        (Fraction.Field.zero_add _).symm
      _ ≤ value.re ^ 2 + value.im ^ 2 := added
      _ = Data.Gaussian.Norm.Basic.normSq value := rfl
  have realSquareBound := realSquare.trans normBound
  have imaginarySquareBound := imaginarySquare.trans normBound
  have realUpper : value.re ≤ bound + 1 :=
    (Quadratic.coordinate_le_sq_add_one value.re).trans
      (Fraction.Order.Arithmetic.add_le_add_right_direct realSquareBound 1)
  have realNegUpper : -value.re ≤ bound + 1 :=
    (Quadratic.neg_coordinate_le_sq_add_one value.re).trans
      (Fraction.Order.Arithmetic.add_le_add_right_direct realSquareBound 1)
  have imaginaryUpper : value.im ≤ bound + 1 :=
    (Quadratic.coordinate_le_sq_add_one value.im).trans
      (Fraction.Order.Arithmetic.add_le_add_right_direct imaginarySquareBound 1)
  have imaginaryNegUpper : -value.im ≤ bound + 1 :=
    (Quadratic.neg_coordinate_le_sq_add_one value.im).trans
      (Fraction.Order.Arithmetic.add_le_add_right_direct imaginarySquareBound 1)
  exact ⟨by
      simpa only [_root_.neg_neg] using
        Fraction.Order.Arithmetic.neg_le_neg_direct realNegUpper,
    realUpper,
    by
      simpa only [_root_.neg_neg] using
        Fraction.Order.Arithmetic.neg_le_neg_direct imaginaryNegUpper,
    imaginaryUpper⟩
end Purelib.Data.Gaussian.NormSq

end
